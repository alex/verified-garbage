import VerifiedGarbage.Proof.AesGcm.X86.StreamAad
import VerifiedGarbage.Proof.AesGcm.X86.StreamInit
import VerifiedGarbage.Proof.AesGcm.X86.StreamDecrypt
import VerifiedGarbage.Proof.AesGcm.X86.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86.StreamVerify
import VerifiedGarbage.Proof.AesGcm.X86.Init
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean`: with 28 bytes of stack for the functions that call
`vg_aes_ctr32` (which pushes six arguments, and the return address), and 24
for `stream_init` and `stream_aad`, which call only `vg_ghash` (five).
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.Impl.AesGcm.X86

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no
data): the context at `0x1000`, the state at `0x3000`, the data at `0x2000`
and `scratch` at `0x4000`, as stack arguments at `0x8004`. -/
def saSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x8015 then 0x20 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 28⟩]

theorem streamAad_verified : Verified X86.target streamAad (Spec.Gcm.streamAadContract X86.abi 24) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    have a0 : arg saSat 0 = 0x1000 := by decide
    have a1 : arg saSat 1 = 0x3000 := by decide
    have a2 : arg saSat 2 = 0 := by decide
    have a3 : arg saSat 3 = 0 := by decide
    have a4 : arg saSat 4 = 0x2000 := by decide
    have a5 : arg saSat 5 = 0 := by decide
    have a6 : arg saSat 6 = 0x4000 := by decide
    have e : argAddr saSat 0 = 0x8004 := by decide
    have esp : saSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, streamAadX86, streamAadPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using saSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no
nonce): the context at `0x1000`, the nonce at `0x2000`, the state at
`0x3000` and `scratch` at `0x4000`. -/
def siSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x30 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 20⟩]

theorem streamInit_verified : Verified X86.target streamInit (Spec.Gcm.streamInitContract X86.abi 24) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    have a0 : arg siSat 0 = 0x1000 := by decide
    have a1 : arg siSat 1 = 0x2000 := by decide
    have a2 : arg siSat 2 = 0 := by decide
    have a3 : arg siSat 3 = 0x3000 := by decide
    have a4 : arg siSat 4 = 0x4000 := by decide
    have e : argAddr siSat 0 = 0x8004 := by decide
    have esp : siSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, streamInitX86, streamInitPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, e, esp] using siSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and
`_decrypt` (with no data): the context at `0x1000`, 10 rounds, the state at
`0x3000`, the data at `0x2000` and `scratch` at `0x4000`. -/
def crSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x20 else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

theorem streamEncrypt_verified : Verified X86.target streamEncrypt (Spec.Gcm.streamEncryptContract X86.abi 28) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 10 := by decide
    have a2 : arg crSat 2 = 0x3000 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0 := by decide
    have a7 : arg crSat 7 = 0x2000 := by decide
    have a8 : arg crSat 8 = 0 := by decide
    have a9 : arg crSat 9 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, streamEncryptX86, streamCryptPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using crSat)

theorem streamDecrypt_verified : Verified X86.target streamDecrypt (Spec.Gcm.streamDecryptContract X86.abi 28) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 10 := by decide
    have a2 : arg crSat 2 = 0x3000 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0 := by decide
    have a7 : arg crSat 7 = 0x2000 := by decide
    have a8 : arg crSat 8 = 0 := by decide
    have a9 : arg crSat 9 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, streamDecryptX86, streamCryptPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using crSat)

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition: the
context at `0x1000`, 10 rounds, the state at `0x3000` and `work` at
`0x4000`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 32⟩]

theorem streamFinish_verified : Verified X86.target streamFinish (Spec.Gcm.streamFinishContract X86.abi 28) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    have a0 : arg finSat 0 = 0x1000 := by decide
    have a1 : arg finSat 1 = 10 := by decide
    have a2 : arg finSat 2 = 0x3000 := by decide
    have a3 : arg finSat 3 = 0 := by decide
    have a4 : arg finSat 4 = 0 := by decide
    have a5 : arg finSat 5 = 0 := by decide
    have a6 : arg finSat 6 = 0 := by decide
    have a7 : arg finSat 7 = 0x4000 := by decide
    have e : argAddr finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, streamFinishX86, finPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using finSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition: as
`finSat`, with a `tag_len` of 0. -/
def verSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x30
    else if a = 0x8021 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamVerify_verified : Verified X86.target streamVerify (Spec.Gcm.streamVerifyContract X86.abi 28) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    have a0 : arg verSat 0 = 0x1000 := by decide
    have a1 : arg verSat 1 = 10 := by decide
    have a2 : arg verSat 2 = 0x3000 := by decide
    have a3 : arg verSat 3 = 0 := by decide
    have a4 : arg verSat 4 = 0 := by decide
    have a5 : arg verSat 5 = 0 := by decide
    have a6 : arg verSat 6 = 0 := by decide
    have a7 : arg verSat 7 = 0x4000 := by decide
    have a8 : arg verSat 8 = 0 := by decide
    have e : argAddr verSat 0 = 0x8004 := by decide
    have esp : verSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, streamVerifyX86, verifyPre, pubN,
      roundsOk, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using verSat)

/-- A state satisfying `vg_aes_gcm_init`'s precondition: a 16-byte key at
`0x1000`, the context at `0x2000` and `scratch` at `0x4000`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem init_verified : Verified X86.target init (Spec.Gcm.initContract X86.abi 28) :=
  Verified.of_correct init_correct init_ct (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 16 := by decide
    have a2 : arg initSat 2 = 0x2000 := by decide
    have a3 : arg initSat 3 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, initX86, initPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using initSat)

end VG.Proof.AesGcm.X86
