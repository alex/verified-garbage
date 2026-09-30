import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst

/-!
# ML-DSA signing on x86-64: verified

Untrusted: everything here is checked by Lean. `vg_mldsa{44,65,87}_sign`
(`sign prims p`) is verified against `signContractT`: `signContract` with
`signLeakT` (`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what
each iteration of the loop leaks after its `c̃` with whether it was
rejected. **It is not verified against `signContract`**, whose leakage does
not say where the iterations end: after the `c̃` of an iteration that
passes, the hint (`256 k` numbers, each 0 or 1) is the same list as the
`c̃`s (of `λ / 4` bytes each, `256 k = 32 · λ / 4` for every parameter set)
of 32 more rejected iterations whose bytes are all 0 or 1, the last of
which has no `SampleInBall` within `maxBounds` (which leaks nothing more).
Two runs so related agree on `signLeak` but not on whether the first
passed, which the code branches on, so no implementation of the loop that
branches on the checks is constant time under `signContract`'s `pub`.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
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
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x3100 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (signContractT p X86_64.abi signStack).pre s) :
    (signK p signStack).Implies (signContractT p X86_64.abi signStack) where
  pre := by sig_implies_pre [signContractT, signSig, signK, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [signContractT, signSig, signK, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContractT, signSig, signK, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : Ok3 p) :
    (signK p signStack).Implies (signContractT p X86_64.abi signStack) := by
  refine signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa44
  · sig_implies_sat [signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa65
  · sig_implies_sat [signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa87

theorem sign_verified {p : Params} (h3 : Ok3 p)
    (hmx : (Impl.MlDsa.X86_64.Sign.sign prims p).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign prims p) (signContractT p X86_64.abi signStack) :=
  Verified.of_correct (sign_correct prims_ok h3 hmx) (sign_ct prims_ok h3) (signK_implies h3)

theorem sign44_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign prims mlDsa44) (signContractT mlDsa44 X86_64.abi signStack) :=
  sign_verified (.inl rfl) (by decide +kernel)

theorem sign65_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign prims mlDsa65) (signContractT mlDsa65 X86_64.abi signStack) :=
  sign_verified (.inr (.inl rfl)) (by decide +kernel)

theorem sign87_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign prims mlDsa87) (signContractT mlDsa87 X86_64.abi signStack) :=
  sign_verified (.inr (.inr rfl)) (by decide +kernel)

/-! What registering them needs of the code besides: it never writes the stack pointer. -/

theorem sign44_spSafe : (Impl.MlDsa.X86_64.Sign.sign prims mlDsa44).all (fun i => !X86_64.target.isa.writesSp i) = true :=
  Code.all_of_allInstrs (by decide +kernel)

theorem sign65_spSafe : (Impl.MlDsa.X86_64.Sign.sign prims mlDsa65).all (fun i => !X86_64.target.isa.writesSp i) = true :=
  Code.all_of_allInstrs (by decide +kernel)

theorem sign87_spSafe : (Impl.MlDsa.X86_64.Sign.sign prims mlDsa87).all (fun i => !X86_64.target.isa.writesSp i) = true :=
  Code.all_of_allInstrs (by decide +kernel)

end VG.Proof.MlDsa.X86_64.Sign
