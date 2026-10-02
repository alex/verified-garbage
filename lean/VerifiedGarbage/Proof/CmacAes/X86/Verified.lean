import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
import VerifiedGarbage.Proof.CmacAes.X86.SubkeysCT
import VerifiedGarbage.Proof.CmacAes.X86.FinalizeCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 28 bytes of stack: each
call of `vg_aes_ctr32` pushes its six arguments and the return address.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition: the schedule
at `0x1000`, 10 rounds, the subkeys at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def subSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified : Verified X86.target subkeys (Spec.Cmac.aesSubkeysContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => subkeys_wp hs) subkeys_ct (by
    have a0 : arg subSat 0 = 0x1000 := by decide
    have a1 : arg subSat 1 = 10 := by decide
    have a2 : arg subSat 2 = 0x2000 := by decide
    have a3 : arg subSat 3 = 0x4000 := by decide
    have e : argAddr subSat 0 = 0x8004 := by decide
    have esp : subSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, subkeysX86] [a0, a1, a2, a3, e, esp] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition: the key at
`0x1000`, 10 rounds, the state at `0x2000`, no last bytes at `0x3000` and
the scratch buffer at `0x4000`, as stack arguments at `0x8004`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified : Verified X86.target finalize (Spec.Cmac.aesFinalizeContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => finalize_wp hs) finalize_ct (by
    have a0 : arg finSat 0 = 0x1000 := by decide
    have a1 : arg finSat 1 = 10 := by decide
    have a2 : arg finSat 2 = 0x2000 := by decide
    have a3 : arg finSat 3 = 0x3000 := by decide
    have a4 : arg finSat 4 = 0 := by decide
    have a5 : arg finSat 5 = 0x4000 := by decide
    have e : argAddr finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, finalizeX86] [a0, a1, a2, a3, a4, a5, e, esp] using finSat)

/-- A state satisfying `vg_cmac_aes_update`'s precondition: as `finSat`,
with no blocks. -/
def updSat : State := { finSat with rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩, ⟨0x8004, 24⟩] }

theorem update_verified : Verified X86.target update (Spec.Cmac.aesUpdateContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => update_wp hs) update_ct (by
    have a0 : arg updSat 0 = 0x1000 := by decide
    have a1 : arg updSat 1 = 10 := by decide
    have a2 : arg updSat 2 = 0x2000 := by decide
    have a3 : arg updSat 3 = 0x3000 := by decide
    have a4 : arg updSat 4 = 0 := by decide
    have a5 : arg updSat 5 = 0x4000 := by decide
    have e : argAddr updSat 0 = 0x8004 := by decide
    have esp : updSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, updateX86] [a0, a1, a2, a3, a4, a5, e, esp] using updSat)

end VG.Proof.CmacAes.X86
