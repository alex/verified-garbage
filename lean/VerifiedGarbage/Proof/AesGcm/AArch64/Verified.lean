import Mathlib.Data.List.Dedup
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.InitCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInitCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamAadCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.FinCT
import VerifiedGarbage.Proof.AesGcm.AArch64.SealCT
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

/-- The CPU features of the functions calling `vg_aes_ctr32` and `vg_ghash`
(here, not in `Callee.lean`, to keep `List.dedup`'s imports out of the proofs). -/
def GcmImpl.features (v : GcmImpl) : List String := (v.ctr.features ++ v.gh.features).dedup

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-! ## v8–v15 -/

theorem init_keepsV (v : GcmImpl) : (init v.callees).allInstrs keepsV = true := by
  simp only [init, ctrCall, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamInit_keepsV (v : GcmImpl) : (streamInit v.callees).allInstrs keepsV = true := by
  simp only [streamInit, j0, j0hash, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamAad_keepsV (v : GcmImpl) : (streamAad v.callees).allInstrs keepsV = true := by
  simp only [streamAad, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamEncrypt_keepsV (v : GcmImpl) : (streamEncrypt v.callees).allInstrs keepsV = true := by
  simp only [streamEncrypt, encBody, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb,
    absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamDecrypt_keepsV (v : GcmImpl) : (streamDecrypt v.callees).allInstrs keepsV = true := by
  simp only [streamDecrypt, decBody, decAbs, fo, textAbs, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall,
    absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamFinish_keepsV (v : GcmImpl) : (streamFinish v.callees).allInstrs keepsV = true := by
  simp only [streamFinish, finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1,
    absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV,
    v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem streamVerify_keepsV (v : GcmImpl) : (streamVerify v.callees).allInstrs keepsV = true := by
  simp only [streamVerify, tagLenOk, tlTest, cmpSeg, finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall,
    ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees, Code.allInstrs,
    v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem seal_keepsV (v : GcmImpl) : («seal» v.callees).allInstrs keepsV = true := by
  simp only [«seal», j0, j0hash, oneAad, encBody, fo, textAbs, finBody, tag, crypt, crSeg1, crSeg2, crTail,
    ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor, padSeg, flush, lens, GcmImpl.callees,
    Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]; decide +kernel

theorem open_keepsV (v : GcmImpl) : («open» v.callees).allInstrs keepsV = true := by
  simp only [«open», openMain, oneCrypt, tagLenOk, tlTest, cmpSeg, j0, j0hash, oneAad, decAbs, fo, textAbs,
    finBody, tag, crypt, crSeg1, crSeg2, crTail, ctrCall, ghCall, absorb, absSeg1, absTail, minK, copy, Impl.AesGcm.AArch64.xor,
    padSeg, flush, lens, GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV, v.gh.keepsV]
  decide +kernel

/-! ## Correctness -/

theorem init_correct (v : GcmImpl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.callees) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

theorem streamInit_correct (v : GcmImpl) (s : State) (hs : streamInitAArch64.pre s) :
    ∃ t s', Exec isa (streamInit v.callees) s t s' ∧ abiPreserved s s' ∧ streamInitAArch64.post s s' :=
  WP.withPreservedV (streamInit_wp v hs) (streamInit_keepsV v)

theorem streamAad_correct (v : GcmImpl) (s : State) (hs : streamAadAArch64.pre s) :
    ∃ t s', Exec isa (streamAad v.callees) s t s' ∧ abiPreserved s s' ∧ streamAadAArch64.post s s' :=
  WP.withPreservedV (streamAad_wp v hs) (streamAad_keepsV v)

theorem streamEncrypt_correct (v : GcmImpl) (s : State) (hs : streamEncryptAArch64.pre s) :
    ∃ t s', Exec isa (streamEncrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptAArch64.post s s' :=
  WP.withPreservedV (streamEncrypt_wp v hs) (streamEncrypt_keepsV v)

theorem streamDecrypt_correct (v : GcmImpl) (s : State) (hs : streamDecryptAArch64.pre s) :
    ∃ t s', Exec isa (streamDecrypt v.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptAArch64.post s s' :=
  WP.withPreservedV (streamDecrypt_wp v hs) (streamDecrypt_keepsV v)

theorem streamFinish_correct (v : GcmImpl) (s : State) (hs : streamFinishAArch64.pre s) :
    ∃ t s', Exec isa (streamFinish v.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishAArch64.post s s' :=
  WP.withPreservedV (streamFinish_wp v hs) (streamFinish_keepsV v)

theorem streamVerify_correct (v : GcmImpl) (s : State) (hs : streamVerifyAArch64.pre s) :
    ∃ t s', Exec isa (streamVerify v.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyAArch64.post s s' :=
  WP.withPreservedV (streamVerify_wp v hs) (streamVerify_keepsV v)

theorem seal_correct (v : GcmImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callees) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : GcmImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callees) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x3 => 0x2000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x2000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩]

def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified (v : GcmImpl) :
    Verified AArch64.target (init v.callees) (Spec.Gcm.initContract AArch64.abi) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, initAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [initSat] using initSat)

theorem streamInit_verified (v : GcmImpl) :
    Verified AArch64.target (streamInit v.callees) (Spec.Gcm.streamInitContract AArch64.abi) :=
  Verified.of_correct (streamInit_correct v) (streamInit_ct v) (by
    sig_implies [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, streamInitAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified (v : GcmImpl) :
    Verified AArch64.target (streamAad v.callees) (Spec.Gcm.streamAadContract AArch64.abi) :=
  Verified.of_correct (streamAad_correct v) (streamAad_ct v) (by
    sig_implies [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, streamAadAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamEncrypt v.callees) (Spec.Gcm.streamEncryptContract AArch64.abi) :=
  Verified.of_correct (streamEncrypt_correct v) (streamEncrypt_ct v) (by
    sig_implies [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, streamEncryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified (v : GcmImpl) :
    Verified AArch64.target (streamDecrypt v.callees) (Spec.Gcm.streamDecryptContract AArch64.abi) :=
  Verified.of_correct (streamDecrypt_correct v) (streamDecrypt_ct v) (by
    sig_implies [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, streamDecryptAArch64, streamCryptPre, streamCryptPub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified (v : GcmImpl) :
    Verified AArch64.target (streamFinish v.callees) (Spec.Gcm.streamFinishContract AArch64.abi) :=
  Verified.of_correct (streamFinish_correct v) (streamFinish_ct v) (by
    sig_implies [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, streamFinishAArch64, finPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [finSat] using finSat)

theorem streamVerify_verified (v : GcmImpl) :
    Verified AArch64.target (streamVerify v.callees) (Spec.Gcm.streamVerifyContract AArch64.abi) :=
  Verified.of_correct (streamVerify_correct v) (streamVerify_ct v) (by
    sig_implies [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, streamVerifyAArch64, finPre, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [finSat] using finSat)

theorem seal_verified (v : GcmImpl) :
    Verified AArch64.target («seal» v.callees) (Spec.Gcm.sealContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Spec.Gcm.sealContract, Spec.Gcm.sealSig, sealAArch64, onePre, onePub, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified AArch64.target («open» v.callees) (Spec.Gcm.openContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Spec.Gcm.openContract, Spec.Gcm.openSig, openAArch64, onePre, onePub, openRes, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.AesGcm.AArch64
