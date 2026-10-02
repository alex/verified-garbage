import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# TDEA-CMAC on x86: the shared contracts imply ours

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition: a 16-byte
key at `0x1000`, the output at `0x2000` and the scratch buffer at `0x4000`,
as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86.Implies (Spec.Cmac.tdesInitContract X86.abi 0) := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 16 := by decide
  have a2 : arg initSat 2 = 0x2000 := by decide
  have a3 : arg initSat 3 = 0x4000 := by decide
  have e : argAddr initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, initX86] [a0, a1, a2, a3, e, esp] using initSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition: the key
at `0x1000`, the state at `0x2000`, no last bytes at `0x3000` and the
scratch buffer at `0x4000`, as stack arguments at `0x8004`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x800d then 0x30 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeX86.Implies (Spec.Cmac.tdesFinalizeContract X86.abi 0) := by
  have a0 : arg finSat 0 = 0x1000 := by decide
  have a1 : arg finSat 1 = 0x2000 := by decide
  have a2 : arg finSat 2 = 0x3000 := by decide
  have a3 : arg finSat 3 = 0 := by decide
  have a4 : arg finSat 4 = 0x4000 := by decide
  have e : argAddr finSat 0 = 0x8004 := by decide
  have esp : finSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, finalizeX86] [a0, a1, a2, a3, a4, e, esp] using finSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition: as
`finSat`, with no blocks. -/
def updSat : State := { finSat with rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] }

theorem update_implies : updateX86.Implies (Spec.Cmac.tdesUpdateContract X86.abi 0) := by
  have a0 : arg updSat 0 = 0x1000 := by decide
  have a1 : arg updSat 1 = 0x2000 := by decide
  have a2 : arg updSat 2 = 0x3000 := by decide
  have a3 : arg updSat 3 = 0 := by decide
  have a4 : arg updSat 4 = 0x4000 := by decide
  have e : argAddr updSat 0 = 0x8004 := by decide
  have esp : updSat.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, updateX86] [a0, a1, a2, a3, a4, e, esp] using updSat

end VG.Proof.CmacTripleDes.X86
