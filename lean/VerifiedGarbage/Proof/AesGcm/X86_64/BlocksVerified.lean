import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM on whole blocks, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks` (for any
implementations `v` of `vg_aes_ctr32` and `vg_ghash`, with or without the
interleaved loops), a state satisfying their precondition, and the shared
contracts of `Spec/Gcm/Contract.lean` (with 64 bytes of stack: the frame of
the arguments, and the return address of a call; the functions called make
no calls).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

section
variable (v : GcmImpl) (stitch : Bool)

theorem encryptBlocks_mx :
    (Blocks.encrypt v.callees.ctr v.callees.gh stitch).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases stitch <;>
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem decryptBlocks_mx :
    (Blocks.decrypt v.callees.ctr v.callees.gh stitch).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases stitch <;>
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem encryptBlocks_spSafe :
    (Blocks.encrypt v.callees.ctr v.callees.gh stitch).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases stitch <;>
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all,
    GcmImpl.callees, v.ctr.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem decryptBlocks_spSafe :
    (Blocks.decrypt v.callees.ctr v.callees.gh stitch).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases stitch <;>
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all,
    GcmImpl.callees, v.ctr.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true] <;> decide +kernel

theorem encryptBlocks_correct (s : State) (hs : Proof.AesGcm.encryptBlocksX86_64.pre s) :
    ∃ t s', Exec isa (Blocks.encrypt v.callees.ctr v.callees.gh stitch) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.encryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.encrypt_wp v stitch hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptBlocks_mx v stitch) he hg, hp⟩

theorem decryptBlocks_correct (s : State) (hs : Proof.AesGcm.decryptBlocksX86_64.pre s) :
    ∃ t s', Exec isa (Blocks.decrypt v.callees.ctr v.callees.gh stitch) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.decryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.decrypt_wp v stitch hs
  exact ⟨t, s', he, abiPreserved_of_exec (decryptBlocks_mx v stitch) he hg, hp⟩

end

/-- A state satisfying the precondition of `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks` (with no
data, and `scratch` at 0). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 0⟩, ⟨0, 2048⟩]

theorem encryptBlocks_verified (v : GcmImpl) (stitch : Bool) :
    Verified X86_64.target (Blocks.encrypt v.callees.ctr v.callees.gh stitch)
      (Spec.Gcm.encryptBlocksContract X86_64.abi 64) :=
  Verified.of_correct (encryptBlocks_correct v stitch) (Blocks.encrypt_ct v stitch) (by
    sig_implies [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64,
      Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk64, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified (v : GcmImpl) (stitch : Bool) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh stitch)
      (Spec.Gcm.decryptBlocksContract X86_64.abi 64) :=
  Verified.of_correct (decryptBlocks_correct v stitch) (Blocks.decrypt_ct v stitch) (by
    sig_implies [Spec.Gcm.decryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.decryptBlocksX86_64,
      Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk64, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.AesGcm.X86_64
