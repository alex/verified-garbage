import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Init
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.AbsorbCT
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Finish
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# Streaming AES-CMAC on ARMv7: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`: with 8 bytes of stack for
`init` (the frame of `vg_cmac_aes_subkeys`), and 16 for `absorb` and `finish`
(the stack arguments they push, and the frame of the function they call below
them).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 16 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified Arm.target init (Spec.Cmac.aesInitContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, initArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data):
`state` at `0x1000`, `data` at `0x3000`, `scratch` at `0x4000`, the stack
arguments at `0x8000`. -/
def absorbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else if a = 0x8009 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified Arm.target absorb (Spec.Cmac.aesAbsorbContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => absorb_wp hs) absorb_ct (by
    sig_implies [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, absorbArm, countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition: `state` at
`0x1000`, `out` at `0x2000`, `scratch` at `0x4000`, the stack arguments at
`0x8000`. -/
def finishSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8005 then 0x40 else 0
  rd := [⟨0x8000, 8⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified Arm.target finish (Spec.Cmac.aesFinishContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => finish_wp hs) finish_ct (by
    sig_implies [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, finishArm, countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finishSat)

end VG.Proof.CmacAes.Stream.Arm
