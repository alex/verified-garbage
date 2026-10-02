import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same

/-!
# ML-DSA signing on x86-64: verified

Untrusted: everything here is checked by Lean. `vg_mldsa{44,65,87}_sign`
(`sign (primsWith v.code) p`, for an implementation `v` of the polynomial
arithmetic) is verified against `signContractT`: `signContract` with
`signLeakT` (`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what
each iteration of the loop leaks after its `c̃` with whether it was
rejected. The contract's `signLeak` tags the iterations the same way
(`signLeakT_eq_signLeak`), so `signContractT` is `signContract`
(`signContractT_eq`), against which `sign*_verified'` state it.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

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

/-! ## For any implementation of the polynomial arithmetic

A check that composes over the code (`Comp`) gives the same result on
signing with the polynomial arithmetic `B` as with every function of it
empty, if it holds of `B`'s functions (`sign_same`), so MXCSR (`sign_ctl`)
and the stack pointer (`sign_spSafe`) are checked by evaluating signing
with no implementation of it. -/

theorem sign_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h2 : mc B.invNtt = true) (h3 : mc B.mul = true) (h4 : mc B.mulAdd = true) (h5 : mc B.add = true)
    (h6 : mc B.sub = true) (h8 : mc B.highBits = true) (h9 : mc B.lowBits = true)
    (h10 : mc B.normLt = true) (h11 : mc B.makeHint = true) (p : Params) :
    Same m (Impl.MlDsa.X86_64.Sign.sign (primsWith B) p) (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) := by
  unfold Impl.MlDsa.X86_64.Sign.sign
  same_tac hm

theorem sign0_ctlC {p : Params} (h3 : Ok3 p) : ctlC (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem sign0_sp {p : Params} (h3 : Ok3 p) :
    (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

variable (v : ArithImpl) {p : Params} (h3 : Ok3 p)
include h3

theorem sign_ctl : ctlOk (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) = true :=
  ctlOk_of_ctlC (Same.ok (sign_same Comp.ctlC v.ok.ntt.ctl v.ok.invNtt.ctl v.ok.mul.ctl v.ok.mulAdd.ctl
    v.ok.add.ctl v.ok.sub.ctl v.ok.highBits.ctl v.ok.lowBits.ctl v.ok.normLt.ctl v.ok.makeHint.ctl p) (sign0_ctlC h3))

theorem sign_spSafe : (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (sign_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.invNtt.sp) (Code.allInstrs_of_all v.ok.mul.sp)
    (Code.allInstrs_of_all v.ok.mulAdd.sp) (Code.allInstrs_of_all v.ok.add.sp)
    (Code.allInstrs_of_all v.ok.sub.sp)
    (Code.allInstrs_of_all v.ok.highBits.sp) (Code.allInstrs_of_all v.ok.lowBits.sp)
    (Code.allInstrs_of_all v.ok.normLt.sp) (Code.allInstrs_of_all v.ok.makeHint.sp) p) (sign0_sp h3))

theorem sign_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) (signContractT p X86_64.abi signStack) :=
  Verified.of_correct (sign_correct (prims_okWith v) h3 (sign_ctl v h3)) (sign_ct (prims_okWith v) h3)
    (signK_implies h3)

omit h3 in
/-- Against the contract: `signContractT` is `signContract`, whose leakage
tags each iteration as `signLeakT` does (`signLeakT_eq_signLeak`). -/
theorem signContractT_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signContractT p A stack = signContract p A stack := by
  unfold signContractT signContract
  simp only [Sign.signLeakT_eq_signLeak]

theorem sign_verified' :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) (signContract p X86_64.abi signStack) :=
  signContractT_eq p X86_64.abi signStack ▸ sign_verified v h3

end VG.Proof.MlDsa.X86_64.Sign
