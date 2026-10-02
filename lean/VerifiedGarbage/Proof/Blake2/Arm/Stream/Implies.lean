import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# Streaming BLAKE2 on ARMv7: the shared contracts

The ARMv7 contracts of the streaming functions (`initArm`, `updateArm`,
`finalizeArm`) imply the shared ones (`Spec/Blake2/Contract.lean`) on
`Arm.abi`, for BLAKE2b and BLAKE2s, with states satisfying their
preconditions.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Proof.Blake2 (initArm updateArm finalizeArm)

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key: `state` at `0x1000`. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update`, with no data, for `w`-bit words: `state` at `0x1000`, `data` at
`0x2000`, `scratch` at `0x3000`, the stack arguments at `0x5000`. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5009 then 0x30 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x5000, 12⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words: `state` at `0x1000`, `out` at `0x2000`,
`scratch` at `0x3000`, the stack arguments at `0x5000`. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_implies : (initArm b).Implies (Spec.Blake2.initBContract Arm.abi) := by
  contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using initSat 64

theorem updateB_implies : (updateArm b).Implies (Spec.Blake2.updateBContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig, Proof.Blake2.updateArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updateSat 64

theorem finalizeB_implies : (finalizeArm b).Implies (Spec.Blake2.finalizeBContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig, Proof.Blake2.finalizeArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finalizeSat 64

/-! ## BLAKE2s -/

theorem initS_implies : (initArm s).Implies (Spec.Blake2.initSContract Arm.abi) := by
  contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using initSat 32

theorem updateS_implies : (updateArm s).Implies (Spec.Blake2.updateSContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.updateSContract, Spec.Blake2.updateSSig, Proof.Blake2.updateArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updateSat 32

theorem finalizeS_implies : (finalizeArm s).Implies (Spec.Blake2.finalizeSContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.finalizeSContract, Spec.Blake2.finalizeSSig, Proof.Blake2.finalizeArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finalizeSat 32

end VG.Proof.Blake2.Arm.Stream
