import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCT
import VerifiedGarbage.Proof.CmacAes.Arm.SubkeysCT
import VerifiedGarbage.Proof.CmacAes.Arm.FinalizeCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean`, with 8 bytes of stack: each call of
`vg_aes_ctr32` pushes its two stack arguments.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks,
and the scratch buffer at 0, which the zero stack arguments point at). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem update_verified : Verified Arm.target update (Spec.Cmac.aesUpdateContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => update_wp hs) update_ct (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x3000, 2176⟩]

theorem subkeys_verified : Verified Arm.target subkeys (Spec.Cmac.aesSubkeysContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => subkeys_wp hs) subkeys_ct (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last
bytes, and the scratch buffer at 0). -/
def finSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0, 2176⟩]

theorem finalize_verified : Verified Arm.target finalize (Spec.Cmac.aesFinalizeContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => finalize_wp hs) finalize_ct (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finSat)

end VG.Proof.CmacAes.Arm
