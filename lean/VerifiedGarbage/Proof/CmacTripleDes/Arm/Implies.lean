import VerifiedGarbage.Proof.CmacTripleDes.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# TDEA-CMAC on ARMv7: the shared contracts imply ours

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initArm.Implies (Spec.Cmac.tdesInitContract Arm.abi 0) := by
  sig_implies [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, initArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no
blocks, and the scratch buffer at 0). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0, 640⟩]

theorem update_implies : updateArm.Implies (Spec.Cmac.tdesUpdateContract Arm.abi 0) := by
  sig_implies [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, updateArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no
last bytes, and the scratch buffer at 0). -/
def finSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0, 640⟩]

theorem finalize_implies : finalizeArm.Implies (Spec.Cmac.tdesFinalizeContract Arm.abi 0) := by
  sig_implies [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, finalizeArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finSat

end VG.Proof.CmacTripleDes.Arm
