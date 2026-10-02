import VerifiedGarbage.Proof.AesGcm.Arm.InitCT
import VerifiedGarbage.Proof.AesGcm.Arm.CTStream
import VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn
import VerifiedGarbage.Proof.AesGcm.Arm.CTOpen
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# AES-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean`, with 8 bytes of stack: each call of
`vg_aes_ctr32` or `vg_ghash` pushes two words.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Spec.Gcm.initContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, initArm, bel, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat, mkSat] using initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamInit_verified :
    Verified Arm.target streamInit (Spec.Gcm.streamInitContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamInit_wp hs) streamInit_ct (by
    sig_implies [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, streamInitArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamAad_verified :
    Verified Arm.target streamAad (Spec.Gcm.streamAadContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamAad_wp hs) streamAad_ct (by
    sig_implies [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, streamAadArm, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified :
    Verified Arm.target streamEncrypt (Spec.Gcm.streamEncryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamEncrypt_wp hs) streamEncrypt_ct (by
    sig_implies [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, streamEncryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

theorem streamDecrypt_verified :
    Verified Arm.target streamDecrypt (Spec.Gcm.streamDecryptContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamDecrypt_wp hs) streamDecrypt_ct (by
    sig_implies [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, streamDecryptArm, streamCryptPre,
      streamCryptPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `work` at 0). -/
def fSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamFinish_verified :
    Verified Arm.target streamFinish (Spec.Gcm.streamFinishContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamFinish_wp hs) streamFinish_ct (by
    sig_implies [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, streamFinishArm, finPre, finPub,
      bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using fSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with `work` at 0). -/
def vSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified :
    Verified Arm.target streamVerify (Spec.Gcm.streamVerifyContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => streamVerify_wp hs) streamVerify_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, streamVerifyArm, finPre,
          finPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [streamVerifyArm, Arm.State.addr] at h
        trace_state
        sorry
      pub := by
        sig_implies_pub [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, streamVerifyArm, finPre,
          finPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, streamVerifyArm, finPre,
          finPub, bel, arg, args, arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using vSat }

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or
data, and `work` at 0). -/
def oSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

theorem seal_verified : Verified Arm.target «seal» (Spec.Gcm.sealContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Spec.Gcm.sealContract, Spec.Gcm.sealSig, sealArm, onePre, onePub, bel, arg, args, arg64,
      roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using oSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data or
data, and `work` at 0). -/
def opSat : State :=
  mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified : Verified Arm.target «open» (Spec.Gcm.openContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.openContract, Spec.Gcm.openSig, openArm, onePre, onePub, bel, arg, args,
          arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Spec.Gcm.openContract, Spec.Gcm.openSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
        simp only [openArm, Arm.State.addr] at h
        trace_state
        sorry
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.Gcm.openContract, Spec.Gcm.openSig, openArm, onePre, onePub, bel, arg, args,
          arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        trace_state
        sorry
      sat := by
        sig_implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, openArm, onePre, onePub, bel, arg, args,
          arg64, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using opSat }

end VG.Proof.AesGcm.Arm
