import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamInitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamAadCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamDecrypt
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts
of `Spec/Gcm/Contract.lean` (with 8 bytes of stack, for the return address
of a call: the functions called make no calls).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String := (v.ctr.features ++ v.gh.features).dedup

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

section
variable (v : GcmImpl)

theorem init_mx : (init v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_spSafe : (init v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem init_correct (s : State) (hs : Proof.AesGcm.initX86_64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

theorem streamInit_mx : (streamInit v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_spSafe : (streamInit v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamInit_correct (s : State) (hs : Proof.AesGcm.streamInitX86_64.pre s) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamInitX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamInit_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamInit_mx v) he hg, hp⟩

theorem streamAad_mx : (streamAad v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_spSafe : (streamAad v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamAad_correct (s : State) (hs : Proof.AesGcm.streamAadX86_64.pre s) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamAadX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamAad_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamAad_mx v) he hg, hp⟩

theorem streamEncrypt_mx : (streamEncrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_spSafe : (streamEncrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncrypt_correct (s : State) (hs : Proof.AesGcm.streamEncryptX86_64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncrypt_mx v) he hg, hp⟩

theorem streamDecrypt_mx : (streamDecrypt v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_spSafe : (streamDecrypt v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecrypt_correct (s : State) (hs : Proof.AesGcm.streamDecryptX86_64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecrypt_mx v) he hg, hp⟩

theorem streamFinish_mx : (streamFinish v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_spSafe : (streamFinish v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamFinish_correct (s : State) (hs : Proof.AesGcm.streamFinishX86_64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamFinishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamFinish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamFinish_mx v) he hg, hp⟩

theorem streamVerify_mx : (streamVerify v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_spSafe : (streamVerify v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneTag, oneCrypt, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamVerify_correct (s : State) (hs : Proof.AesGcm.streamVerifyX86_64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamVerifyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamVerify_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamVerify_mx v) he hg, hp⟩

theorem seal_mx : («seal» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_spSafe : («seal» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem seal_correct (s : State) (hs : Proof.AesGcm.sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_mx : («open» v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := encryptBlocks_mx v v.stitch
  have d := decryptBlocks_mx v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.allInstrs, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := encryptBlocks_spSafe v v.stitch
  have d := decryptBlocks_spSafe v v.stitch
  simp only [GcmImpl.callees] at e d
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», ghash1, absorbHead, absorbWhole, absorbTail, absorb, flush, lens, cryptHead, cryptWhole, cryptTail, crypt, tag, j0hash, j0, firstFlush, textAbsorb, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneUndo, Code.all, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem open_correct (s : State) (hs : Proof.AesGcm.openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

end

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified (v : GcmImpl) :
    Verified X86_64.target (init v.callees) (Spec.Gcm.initContract X86_64.abi 8) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, Proof.AesGcm.initX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamInit_verified (v : GcmImpl) :
    Verified X86_64.target (streamInit v.callees) (Spec.Gcm.streamInitContract X86_64.abi 8) :=
  Verified.of_correct (streamInit_correct v) (streamInit_ct v) (by
    sig_implies [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Proof.AesGcm.streamInitX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [siSat] using siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x2000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamAad_verified (v : GcmImpl) :
    Verified X86_64.target (streamAad v.callees) (Spec.Gcm.streamAadContract X86_64.abi 8) :=
  Verified.of_correct (streamAad_correct v) (streamAad_ct v) (by
    sig_implies [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Proof.AesGcm.streamAadX86_64, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [saSat] using saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no data, and `scratch` at 0). -/
def crSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamEncrypt v.callees) (Spec.Gcm.streamEncryptContract X86_64.abi 8) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified X86_64.target (streamDecrypt v.callees) (Spec.Gcm.streamDecryptContract X86_64.abi 8) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition. -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamFinish_verified (v : GcmImpl) :
    Verified X86_64.target (streamFinish v.callees) (Spec.Gcm.streamFinishContract X86_64.abi 8) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Proof.AesGcm.streamFinishX86_64, Proof.AesGcm.finPre, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [finSat] using finSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition. -/
def verSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

theorem streamVerify_verified (v : GcmImpl) :
    Verified X86_64.target (streamVerify v.callees) (Spec.Gcm.streamVerifyContract X86_64.abi 8) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Proof.AesGcm.streamVerifyX86_64, Proof.AesGcm.verifyPre, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [verSat] using verSat)

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or data, and `work` at 0). -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

theorem seal_verified (v : GcmImpl) :
    Verified X86_64.target («seal» v.callees) (Spec.Gcm.sealContract X86_64.abi 24) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Proof.AesGcm.sealX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data or data, and `work` at 0). -/
def openSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : GcmImpl) :
    Verified X86_64.target («open» v.callees) (Spec.Gcm.openContract X86_64.abi 24) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      post := by sig_implies_post [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs]
        sig_simp [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply leak_bool; with_reducible assumption)
      sat := by sig_implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Proof.AesGcm.openX86_64, Proof.AesGcm.onePre, Proof.AesGcm.onePub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [openSat] using openSat }

end VG.Proof.AesGcm.X86_64
