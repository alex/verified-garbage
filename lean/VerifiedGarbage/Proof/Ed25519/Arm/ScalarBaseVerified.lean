import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseLit
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! The complete base-point multiplier meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def baseSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  scalarBase_correct (ScalarBasePre.of hs)

theorem scalarBase_verified : Verified Arm.target scalarBase
    (Spec.Ed25519.scalarBaseContract Arm.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, scalarBaseLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [baseSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using baseSatState)

end VG.Proof.Ed25519.Arm
