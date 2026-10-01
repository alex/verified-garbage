import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.TCB.Artifact

/-!
# Triple DES ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, round keys and data are secret.
The schedule has 48 little-endian 64-bit slots (384 bytes), in encryption
order for K1, K2 and K3. Expansion zero-extends each 48-bit round key.
Scratch contents are unspecified on return. `stack` accounts for frames
and calls; ECB permits writes to ABI argument areas to call block primitives.

The Rust wrapper will buffer partial blocks, reject invalid key lengths
before key expansion, and reject incomplete input at finalization. It will
not add or remove padding. Empty ECB input is supported.
-/

namespace VG.Spec.TripleDes

def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 384),
    ("scratch", .array true .u64 64)]

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (pre := fun _key keyLen _schedule _scratch _ => validKey keyLen.toNat)
    (post := fun key keyLen schedule _scratch m m' _ =>
      scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat))
    (stack := stack)

def expandKeyApi : Api where
  module := "triple_des"
  name := "vg_triple_des_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "Triple DES key expansion (FIPS 46-3 Appendix 1): expands a 16- or 24-byte key \
    into three encryption-order DES schedules, each containing sixteen 48-bit round keys \
    zero-extended into little-endian 64-bit slots. For a 16-byte key, K3 repeats K1. \
    Parity bits are ignored and weak or repeated component keys are accepted.\n\n\
    Contract: `VG.Spec.TripleDes.expandKeyContract`. Constant time: only pointers and \
    `key_len` may affect timing, not key bytes."
  safety := ["`key_len` must be 16 or 24.", "The contents of `scratch` on return are unspecified."]

def blockSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .array true .u8 8),
    ("scratch", .array true .u64 64)]

def encryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = encryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def encryptBlockApi : Api where
  module := "triple_des"
  name := "vg_triple_des_encrypt_block"
  sig := blockSig
  contracts := some fun A stack => encryptBlockContract A stack
  summary := "Triple DES block encryption (FIPS 46-3): transforms the 8 bytes at `data` \
    in place under the three DES schedules at `schedule`. Each schedule contains sixteen \
    encryption-order 48-bit round keys in little-endian 64-bit slots; upper bits are ignored.\n\n\
    Contract: `VG.Spec.TripleDes.encryptBlockContract`. Constant time: only pointers \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

def decryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = decryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def decryptBlockApi : Api where
  module := "triple_des"
  name := "vg_triple_des_decrypt_block"
  sig := blockSig
  contracts := some fun A stack => decryptBlockContract A stack
  summary := "Triple DES block decryption (FIPS 46-3): transforms the 8 bytes at `data` \
    in place under the three DES schedules at `schedule`. Each schedule contains sixteen \
    encryption-order 48-bit round keys in little-endian 64-bit slots; upper bits are ignored.\n\n\
    Contract: `VG.Spec.TripleDes.decryptBlockContract`. Constant time: only pointers \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

def ecbSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u64 128)]

def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A
    (post := fun schedule data n _scratch m m' _ =>
      blocksAt m' data n.toNat = ecb (scheduleAt m schedule) direction (blocksAt m data n.toNat))
    (writeArgs := true)
    (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbEncryptApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_encrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "Triple DES ECB encryption (SP 800-38A §6.1) of `n` complete 8-byte \
    blocks at `data`, in place, under the schedule written by `vg_triple_des_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbEncryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := ["The contents of `scratch` on return are unspecified."]

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

def ecbDecryptApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_decrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "Triple DES ECB decryption (SP 800-38A §6.1) of `n` complete 8-byte \
    blocks at `data`, in place, under the schedule written by `vg_triple_des_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbDecryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.TripleDes
