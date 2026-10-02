import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT
import VerifiedGarbage.Proof.CmacAes.AArch64.SubkeysCT
import VerifiedGarbage.Proof.CmacAes.AArch64.FinalizeCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem update_keepsV (v : Ctr32Impl) : (update v.callee).allInstrs keepsV = true := by
  simp only [update, body, Code.allInstrs, v.keepsV]; decide +kernel

theorem subkeys_keepsV (v : Ctr32Impl) : (subkeys v.callee).allInstrs keepsV = true := by
  simp only [subkeys, Code.allInstrs, v.keepsV]; decide +kernel

theorem finalize_keepsV (v : Ctr32Impl) : (finalize v.callee).allInstrs keepsV = true := by
  simp only [finalize, finPre, partialBlock, copy, Code.allInstrs, v.keepsV]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  WP.withPreservedV (update_wp v hs) (update_keepsV v)

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysAArch64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysAArch64.post s s' :=
  WP.withPreservedV (subkeys_wp v hs) (subkeys_keepsV v)

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  WP.withPreservedV (finalize_wp v hs) (finalize_keepsV v)

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified AArch64.target (update v.callee) (Spec.Cmac.aesUpdateContract AArch64.abi) :=
  Verified.of_correct (update_correct v) (update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateAArch64, AArch64.abi,
      AArch64.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified AArch64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract AArch64.abi) :=
  Verified.of_correct (subkeys_correct v) (subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysAArch64, AArch64.abi,
      AArch64.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified AArch64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract AArch64.abi) :=
  Verified.of_correct (finalize_correct v) (finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeAArch64, AArch64.abi,
      AArch64.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.AArch64
