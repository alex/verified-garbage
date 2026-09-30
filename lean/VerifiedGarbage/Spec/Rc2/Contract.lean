import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.Artifact

/-!
# RC2-CBC: contracts on every target

**Trusted.** The signatures derive memory validity, non-overlap, permitted
writes and public pointers/lengths from `Sig.contract`. Key bytes, expanded
key words, IV contents and data are secret. Effective key bits are a public
algorithm parameter, independent of the key's byte length.

The schedule is 128 bytes containing 64 little-endian 16-bit words; no
target-specific layout is exposed. Each primitive has separate scratch
space, whose contents are unspecified on return. `stack` describes an
implementation's frames and calls. CBC may also write the argument area
where the ABI permits it, for calls to the block primitive.

The Rust streaming wrapper will initialize the key schedule and IV, buffer
partial blocks between updates, and reject a partial block at finalize.
Only complete blocks reach the CBC primitives; `n = 0` is supported.
-/

namespace VG.Spec.Rc2

/-- `vg_rc2_expand_key(key: *const u8, key_len: usize, effective_bits: usize,
schedule: *mut [u8; 128], scratch: *mut [u64; 64])`. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("effective_bits", .int .usize true),
    ("schedule", .array true .u8 128), ("scratch", .array true .u64 64)]

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (pre := fun _key keyLen effectiveBits _schedule _scratch _ =>
      validKey keyLen.toNat effectiveBits.toNat)
    (post := fun key keyLen effectiveBits schedule _scratch m m' _ =>
      scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat) effectiveBits.toNat)
    (stack := stack)

def expandKeyApi : Api where
  module := "rc2"
  name := "vg_rc2_expand_key"
  sig := expandKeySig
  summary := "RC2 key expansion (RFC 2268 §2): expands the `key_len` bytes at `key` with \
    `effective_bits` effective key bits into `*schedule`, as 64 little-endian 16-bit words. \
    Effective bits are independent of the supplied key length.\n\n\
    Contract: `VG.Spec.Rc2.expandKeyContract`. Constant time: only pointers, `key_len` and \
    `effective_bits` may affect timing, not the key."
  safety := ["`key_len` must be in 1..=128.", "`effective_bits` must be in 1..=1024.",
    "The contents of `scratch` on return are unspecified."]

/-- The block functions:
`(schedule: *const [u8; 128], data: *mut [u8; 8], scratch: *mut [u64; 32])`. -/
def blockSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .array true .u8 8),
    ("scratch", .array true .u64 32)]

def encryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = encryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def decryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = decryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def encryptBlockApi : Api where
  module := "rc2"
  name := "vg_rc2_encrypt_block"
  sig := blockSig
  summary := "RC2 block encryption (RFC 2268 §3): encrypts `*data` in place under \
    `*schedule`, the 64 little-endian 16-bit words written by `vg_rc2_expand_key`.\n\n\
    Contract: `VG.Spec.Rc2.encryptBlockContract`. Constant time: only pointers may affect \
    timing, not the key schedule or data, including the mashing indices."
  safety := ["The contents of `scratch` on return are unspecified."]

def decryptBlockApi : Api where
  module := "rc2"
  name := "vg_rc2_decrypt_block"
  sig := blockSig
  summary := "RC2 block decryption (RFC 2268 §4): decrypts `*data` in place under \
    `*schedule`, the 64 little-endian 16-bit words written by `vg_rc2_expand_key`.\n\n\
    Contract: `VG.Spec.Rc2.decryptBlockContract`. Constant time: only pointers may affect \
    timing, not the key schedule or data, including the reverse-mashing indices."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- The CBC functions:
`(schedule: *const [u8; 128], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize,
scratch: *mut [u64; 64])`. Scratch includes room outside the block
primitive's working space to preserve the chaining value during decryption. -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n"), ("scratch", .array true .u64 64)]

def cbcContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n _scratch m m' _ =>
      let result := cbc (scheduleAt m schedule) direction (blockAt m iv) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = result.1 ∧ blockAt m' iv = result.2)
    (writeArgs := true)
    (stack := stack)

def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .encrypt stack

def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcContract A .decrypt stack

def cbcEncryptApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_encrypt"
  sig := cbcSig
  writeArgs := true
  summary := "RC2-CBC encryption on `n` complete 8-byte blocks at `data`, in place: \
    `C[i] = RC2(schedule, P[i] XOR C[i-1])`, starting with `C[0] = *iv`. \
    Writes the last ciphertext block to `*iv`; for `n = 0`, leaves `*iv` unchanged. \
    The schedule is the 64 little-endian 16-bit words written by `vg_rc2_expand_key`. \
    No padding is added.\n\n\
    Contract: `VG.Spec.Rc2.cbcEncryptContract`. Constant time: only pointers and `n` may \
    affect timing, not the key schedule, IV contents or data."
  safety := ["The contents of `scratch` on return are unspecified."]

def cbcDecryptApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_decrypt"
  sig := cbcSig
  writeArgs := true
  summary := "RC2-CBC decryption on `n` complete 8-byte blocks at `data`, in place: \
    `P[i] = RC2_inverse(schedule, C[i]) XOR C[i-1]`, starting with `C[0] = *iv`. \
    Writes the last input ciphertext block to `*iv`; for `n = 0`, leaves `*iv` unchanged. \
    The schedule is the 64 little-endian 16-bit words written by `vg_rc2_expand_key`. \
    No padding is removed.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptContract`. Constant time: only pointers and `n` may \
    affect timing, not the key schedule, IV contents or data."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Rc2
