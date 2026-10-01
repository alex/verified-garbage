import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCT
import VerifiedGarbage.Proof.CmacAes.X86_64.SubkeysCT
import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/-!
# AES-CMAC on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_aes_ctr32`), a state satisfying each
precondition, and the shared contracts of `Spec/Cmac/Contract.lean` (with
8 bytes of stack, for the return address of the call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem update_mx (v : Ctr32Impl) : (update v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [update, body, Code.allInstrs, v.mxcsr]; decide +kernel

theorem subkeys_mx (v : Ctr32Impl) : (subkeys v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [subkeys, Code.allInstrs, v.mxcsr]; decide +kernel

theorem finalize_mx (v : Ctr32Impl) : (finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finalize, Code.allInstrs, v.mxcsr]; decide +kernel

theorem update_spSafe (v : Ctr32Impl) : (update v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, body, Code.all, v.spSafe]; decide +kernel

theorem subkeys_spSafe (v : Ctr32Impl) : (subkeys v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [subkeys, Code.all, v.spSafe]; decide +kernel

theorem finalize_spSafe (v : Ctr32Impl) : (finalize v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize, Code.all, v.spSafe]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (update_mx v) he hg, hp⟩

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysX86_64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := subkeys_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (subkeys_mx v) he hg, hp⟩

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified X86_64.target (update v.callee) (Spec.Cmac.aesUpdateContract X86_64.abi 8) :=
  Verified.of_correct (update_correct v) (update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateX86_64, X86_64.abi,
      X86_64.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified X86_64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract X86_64.abi 8) :=
  Verified.of_correct (subkeys_correct v) (subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysX86_64, X86_64.abi,
      X86_64.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified X86_64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract X86_64.abi 8) :=
  Verified.of_correct (finalize_correct v) (finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeX86_64, X86_64.abi,
      X86_64.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.X86_64
