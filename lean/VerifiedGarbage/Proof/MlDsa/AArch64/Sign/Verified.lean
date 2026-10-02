import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst

/-!
# ML-DSA signing on AArch64: verified

`vg_mldsa{44,65,87}_sign` (`sign prims p`) is verified against
`signContractT`: `signContract` with `signLeakT`
(`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what each iteration
of the loop leaks after its `c̃` with whether it was rejected. The contract's
`signLeak` tags the iterations the same way (`signLeakT_eq_signLeak`), so
`signContractT` is `signContract` (`signContractT_eq`), against which
`sign*_verified'` state it.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `signContract`, with `signLeakT` for `signLeak`. -/
def signContractT (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeakT p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-- A state satisfying `signContractT`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x3100 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (signContractT p AArch64.abi signStack).pre s) :
    (signK p signStack).Implies (signContractT p AArch64.abi signStack) where
  pre := by sig_implies_pre [signContractT, signSig, signK, AArch64.abi, AArch64.argRegs]
  post := by sig_implies_post [signContractT, signSig, signK, AArch64.abi, AArch64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContractT, signSig, signK, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : Ok3 p) :
    (signK p signStack).Implies (signContractT p AArch64.abi signStack) := by
  refine signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using signSat mlDsa44
  · sig_implies_sat [signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using signSat mlDsa65
  · sig_implies_sat [signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using signSat mlDsa87

theorem sign_verified {p : Params} (h3 : Ok3 p) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) p) (signContractT p AArch64.abi signStack) :=
  Verified.of_correct (sign_correct (keccak := keccak) (prims_okWith (keccak := keccak)) h3) (sign_ct (keccak := keccak) (prims_okWith (keccak := keccak)) h3) (signK_implies h3)

theorem sign44_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa44) (signContractT mlDsa44 AArch64.abi signStack) :=
  sign_verified (.inl rfl)

theorem sign65_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa65) (signContractT mlDsa65 AArch64.abi signStack) :=
  sign_verified (.inr (.inl rfl))

theorem sign87_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa87) (signContractT mlDsa87 AArch64.abi signStack) :=
  sign_verified (.inr (.inr rfl))

/-! Against the contract: `signContractT` is `signContract`, whose leakage
tags each iteration as `signLeakT` does (`signLeakT_eq_signLeak`). -/

theorem signContractT_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signContractT p A stack = signContract p A stack := by
  unfold signContractT signContract
  simp only [Sign.signLeakT_eq_signLeak]

theorem sign44_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa44) (signContract mlDsa44 AArch64.abi signStack) :=
  signContractT_eq mlDsa44 AArch64.abi signStack ▸ sign44_verifiedWith

theorem sign65_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa65) (signContract mlDsa65 AArch64.abi signStack) :=
  signContractT_eq mlDsa65 AArch64.abi signStack ▸ sign65_verifiedWith

theorem sign87_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (primsWith keccak.callee) mlDsa87) (signContract mlDsa87 AArch64.abi signStack) :=
  signContractT_eq mlDsa87 AArch64.abi signStack ▸ sign87_verifiedWith

theorem sign44_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign prims mlDsa44)
      (signContract mlDsa44 AArch64.abi signStack) :=
  sign44_verifiedWith' (keccak := .scalar)

theorem sign65_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign prims mlDsa65)
      (signContract mlDsa65 AArch64.abi signStack) :=
  sign65_verifiedWith' (keccak := .scalar)

theorem sign87_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign prims mlDsa87)
      (signContract mlDsa87 AArch64.abi signStack) :=
  sign87_verifiedWith' (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Sign
