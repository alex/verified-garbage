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

Only complete blocks reach the CBC primitives; `n = 0` is supported.

## Streaming

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_update` and
`vg_rc2_cbc_decrypt_update` implement the streaming model of `Spec/Rc2.lean`
(`initWithEffectiveBits` and `update`) on a context in memory, `contextAt`:
the key schedule, the chaining value and the pending partial block, all
secret. The context's public parts are not stored in it: the caller keeps the
direction (choosing the update function by it) and the number of pending
bytes (`pending_len`, 0 after `init` and `(pending_len + len) % 8` after
each update), and passes the latter to every update. A context therefore
holds nothing an implementation may branch on, as constant time requires.

`init` checks the key length, the effective key bits and the IV length
itself, in `initWithEffectiveBits`'s order, and returns `Error.code` of the
first that fails, or 0: so the verified code decides every outcome of
initialization, although the lengths are public and the caller could check
them. `finalize` has no primitive: `finalize` of a context is
`.ok []` exactly if its pending input is empty, which, by `contextAt`, is
`pending_len = 0`, a public length the caller holds. Unpadded CBC emits
nothing at finalization, and nothing secret is involved.

`init` and the updates take a `scratch` buffer of working space, with room
for that of the primitive each calls (`vg_rc2_expand_key`'s, or the CBC
functions', `[u64; 64]`) and 64 bytes more for what an implementation keeps
across that call. They may overwrite their arguments passed in memory,
where the calling convention allows it (`writeArgs`), to pass arguments to
the primitive they call.
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
  contracts := some fun A stack => expandKeyContract A stack
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
  contracts := some fun A stack => encryptBlockContract A stack
  summary := "RC2 block encryption (RFC 2268 §3): encrypts `*data` in place under \
    `*schedule`, the 64 little-endian 16-bit words written by `vg_rc2_expand_key`.\n\n\
    Contract: `VG.Spec.Rc2.encryptBlockContract`. Constant time: only pointers may affect \
    timing, not the key schedule or data, including the mashing indices."
  safety := ["The contents of `scratch` on return are unspecified."]

def decryptBlockApi : Api where
  module := "rc2"
  name := "vg_rc2_decrypt_block"
  sig := blockSig
  contracts := some fun A stack => decryptBlockContract A stack
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
  contracts := some fun A stack => cbcEncryptContract A stack
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
  contracts := some fun A stack => cbcDecryptContract A stack
  summary := "RC2-CBC decryption on `n` complete 8-byte blocks at `data`, in place: \
    `P[i] = RC2_inverse(schedule, C[i]) XOR C[i-1]`, starting with `C[0] = *iv`. \
    Writes the last input ciphertext block to `*iv`; for `n = 0`, leaves `*iv` unchanged. \
    The schedule is the 64 little-endian 16-bit words written by `vg_rc2_expand_key`. \
    No padding is removed.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptContract`. Constant time: only pointers and `n` may \
    affect timing, not the key schedule, IV contents or data."
  safety := ["The contents of `scratch` on return are unspecified."]

/-! ## Streaming -/

/-- The streaming context at `p` (`[u8; 144]`), for the direction `direction`
and `pendingLen` pending bytes, both of which the caller keeps: the key
schedule in bytes 0–127 (as `scheduleAt`), the chaining value in bytes
128–135, and the pending input in the first `pendingLen` bytes of bytes
136–143. The rest of bytes 136–143 is unspecified. -/
def contextAt (m : Mem) (p : Addr) (direction : Direction) (pendingLen : Nat) : Context where
  schedule := scheduleAt m p
  direction := direction
  iv := blockAt m (p + 128)
  pending := bytesAt m (p + 136) pendingLen

/-- The value `vg_rc2_cbc_init` returns for each error; it returns 0 on
success. -/
def Error.code : Error → Nat
  | .invalidKeyLength => 1
  | .invalidEffectiveBits => 2
  | .invalidIvLength => 3
  | .incompleteBlock => 4

/-- `vg_rc2_cbc_init(key: *const u8, key_len: usize, effective_bits: usize,
iv: *const u8, iv_len: usize, ctx: *mut [u8; 144], scratch: *mut [u64; 72]) -> u32`.
`effective_bits` is public; `scratch` is working space. -/
def cbcInitSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("effective_bits", .int .usize true),
    ("iv", .slice false .u8 "iv_len"), ("ctx", .array true .u8 144),
    ("scratch", .array true .u64 72)]
  ret := some .u32

/-- For any lengths: if `initWithEffectiveBits` of the `key_len` bytes at
`key`, the `iv_len` bytes at `iv` and `effective_bits` succeeds, returns 0
having written its context to `ctx` (`contextAt`, with no pending bytes, for
either direction: the direction is not stored); otherwise returns the code of
its error, and the contents of `ctx` are unspecified. -/
def cbcInitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcInitSig.contract A
    (post := fun key keyLen effectiveBits iv ivLen ctx _scratch m m' r =>
      ∀ direction, match initWithEffectiveBits (bytesAt m key keyLen.toNat)
          (bytesAt m iv ivLen.toNat) direction effectiveBits.toNat with
        | .ok c => r = 0 ∧ contextAt m' ctx direction 0 = c
        | .error e => r.toNat = e.code)
    (writeArgs := true)
    (stack := stack)

def cbcInitApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_init"
  sig := cbcInitSig
  writeArgs := true
  contracts := some fun A stack => cbcInitContract A stack
  summary := "Starts RC2-CBC without padding (RFC 2268, NIST SP 800-38A §6.2), in either \
    direction: checks that `key_len` is in 1..=128, then that `effective_bits` is in \
    1..=1024, then that `iv_len` is 8, and returns 1, 2 or 3 respectively for the first \
    that is not (`VG.Spec.Rc2.Error.code`). Otherwise writes to `*ctx` the context with the key \
    schedule of the `key_len` bytes at `key` with `effective_bits` effective key bits \
    (as `vg_rc2_expand_key`), the `iv_len` bytes at `iv` as the chaining value, and no \
    pending input (`VG.Spec.Rc2.contextAt`), and returns 0. Continue with \
    `vg_rc2_cbc_encrypt_update` or `vg_rc2_cbc_decrypt_update` from 0 pending bytes. \
    Effective bits are independent of the supplied key length.\n\n\
    Contract: `VG.Spec.Rc2.cbcInitContract`. Constant time: only the pointers, `key_len`, \
    `effective_bits` and `iv_len` may affect timing, not the key or the IV."
  safety := [
    "If the function returns nonzero, the contents of `ctx` on return are unspecified.",
    "The contents of `scratch` on return are unspecified."]

/-- The update functions:
`(ctx: *mut [u8; 144], pending_len: usize, data: *const u8, len: usize,
out: *mut u8, out_len: usize, scratch: *mut [u64; 72])`. `pending_len` is
public; `scratch` is working space. `out` is a separate buffer: the output
is longer than `data` when pending bytes complete a block, so it cannot be
`data` in place, and like every writable buffer it overlaps no other. -/
def cbcUpdateSig : Sig where
  params := [("ctx", .array true .u8 144), ("pending_len", .int .usize true),
    ("data", .slice false .u8 "len"), ("out", .slice true .u8 "out_len"),
    ("scratch", .array true .u64 72)]

/-- For `pending_len < 8` and `out_len = (pending_len + len) / 8 * 8`: if
`ctx` holds the context `c` with `pending_len` pending bytes
(`contextAt`), then `update c` of the `len` bytes at `data` writes its
output, the `out_len` bytes of all complete blocks, to `out`, and leaves at
`ctx` its next context, with `(pending_len + len) % 8` pending bytes. -/
def cbcUpdateContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) :
    Contract M :=
  cbcUpdateSig.contract A
    (pre := fun _ctx pendingLen _data len _out outLen _scratch _ =>
      pendingLen.toNat < 8 ∧ outLen.toNat = (pendingLen.toNat + len.toNat) / 8 * 8)
    (post := fun ctx pendingLen data len out outLen _scratch m m' _ =>
      let result := update (contextAt m ctx direction pendingLen.toNat) (bytesAt m data len.toNat)
      contextAt m' ctx direction ((pendingLen.toNat + len.toNat) % 8) = result.1 ∧
        bytesAt m' out outLen.toNat = result.2)
    (writeArgs := true)
    (stack := stack)

def cbcEncryptUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateContract A .encrypt stack

def cbcDecryptUpdateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateContract A .decrypt stack

/-- The `# Safety` items the update functions share. -/
def cbcUpdateSafety : List String := [
  "`pending_len` must be less than 8.",
  "`out_len` must be `(pending_len + len) / 8 * 8`.",
  "The contents of `scratch` on return are unspecified."]

def cbcEncryptUpdateApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_encrypt_update"
  sig := cbcUpdateSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptUpdateContract A stack
  summary := "Continues RC2-CBC encryption without padding: if `*ctx` is a context with \
    `pending_len` pending bytes (`VG.Spec.Rc2.contextAt`, written by `vg_rc2_cbc_init` and \
    updated by this function), encrypts the complete 8-byte blocks of the pending bytes \
    followed by the `len` bytes at `data`, `C[i] = RC2(schedule, P[i] XOR C[i-1])` from the \
    context's chaining value, writes them to `out` (`out_len` bytes), and leaves in `*ctx` \
    the last ciphertext block as the chaining value and the remaining \
    `(pending_len + len) % 8` bytes as the pending input. The caller keeps the number of \
    pending bytes; when the input ends, it is an incomplete block unless it is 0.\n\n\
    Contract: `VG.Spec.Rc2.cbcEncryptUpdateContract`. Constant time: only the pointers, \
    `pending_len`, `len` and `out_len` may affect timing, not the context or the data."
  safety := cbcUpdateSafety

def cbcDecryptUpdateApi : Api where
  module := "rc2"
  name := "vg_rc2_cbc_decrypt_update"
  sig := cbcUpdateSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptUpdateContract A stack
  summary := "Continues RC2-CBC decryption without padding: if `*ctx` is a context with \
    `pending_len` pending bytes (`VG.Spec.Rc2.contextAt`, written by `vg_rc2_cbc_init` and \
    updated by this function), decrypts the complete 8-byte blocks of the pending bytes \
    followed by the `len` bytes at `data`, `P[i] = RC2_inverse(schedule, C[i]) XOR C[i-1]` \
    from the context's chaining value, writes them to `out` (`out_len` bytes), and leaves in \
    `*ctx` the last input ciphertext block as the chaining value and the remaining \
    `(pending_len + len) % 8` bytes as the pending input. The caller keeps the number of \
    pending bytes; when the input ends, it is an incomplete block unless it is 0.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptUpdateContract`. Constant time: only the pointers, \
    `pending_len`, `len` and `out_len` may affect timing, not the context or the data."
  safety := cbcUpdateSafety

end VG.Spec.Rc2
