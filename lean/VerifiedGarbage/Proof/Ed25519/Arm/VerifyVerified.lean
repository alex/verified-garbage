import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCT
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyLit
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! The verification equation meets the reviewed contract and preserves the ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' :=
  verifyEquation_correct (VerifyPre.of hs)

private theorem returnFlag_value (v : BitVec 32) (b : Bool)
    (h : v.toNat = if b then 1 else 0) : v = if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> exact h

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans (returnFlag_value _ _ h)
  pub := by
    sig_implies_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifySatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifySatState

theorem verify_verified : Verified Arm.target verifyEquation (Spec.Ed25519.verifyEquationContract Arm.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.Arm
