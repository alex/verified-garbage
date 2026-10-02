import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of `vg_chacha20_block`
and `vg_chacha20_xor`, in terms of `Spec/ChaCha20.lean`, for any target: `A`
is the target's calling convention. The signatures fix where the arguments
are, the memory each function may access, disjointness, and that the
pointers and lengths are public (see `TCB/Sig.lean`).

`vg_chacha20_xor` may overwrite its arguments passed in memory, where the
calling convention allows it (`writeArgs`), to pass arguments to the
functions it calls, and takes the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`, see
`Sig.contract`).

## Streaming

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` are the
cipher with the 16-byte nonce of `keystreamOf` (the initial block counter
and the RFC 8439 nonce), applied in pieces of any length, on a streaming
state (see `keyAt`, `leftAt`, `restAt`) that holds the key, the position in
the keystream and a partly used block. `init` makes the state represent the
whole keystream of a key and nonce, `set_nonce` that of another nonce with
the same key, and `apply` XORs the next bytes of it into data, or, if fewer
are left (the block counter would pass 2³² − 1), returns 0 and changes
nothing: so the caller keeps no count of its own.

The key, the nonce, the keystream and the data are secret. The number of
bytes of keystream left (`leftAt`) is not: `apply` may leak it (`leak`),
which an implementation needs to branch on the position within a block and
to check the length. It is 64 × (2³² − c) less the bytes applied since the
nonce was set, so it reveals the initial block counter `c` and the total
length applied: in RFC 8439 the block counter is public, as the nonce is
(§2.8 sends the nonce with the ciphertext and starts the counter at 1), and
the lengths of the pieces are public as every length is.

The streaming functions take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`), and
`apply`, which may call `vg_chacha20_xor` and `vg_chacha20_block`, may
overwrite its arguments passed in memory (`writeArgs`). Its implementations
for CPU features (e.g. `vg_chacha20_apply_avx2`) have the same contract.
-/

namespace VG.Spec.ChaCha20

/-- `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`. The
first 16 words of `buf` hold the result on exit; the rest is working space. -/
def blockSig : Sig where
  params := [("state", .array false .u32 16), ("buf", .array true .u32 64)]

/-- Writes `block` of the state at `state` to the first 16 words of `buf`.
The state (key, counter and nonce) is secret. -/
def blockContract {M : ISA} (A : Abi M) : Contract M :=
  blockSig.contract A (post := fun state buf m m' _ =>
    stateAt m' buf = block (stateAt m state))

/-- `vg_chacha20_block` on every target. -/
def blockApi : Api where
  module := "chacha20"
  name := "vg_chacha20_block"
  sig := blockSig
  contracts := some fun A _ => blockContract A
  summary := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
    16-word state `*state` (20 rounds, then the input state added word by word) to the first 16 \
    words of `*buf`.\n\n\
    Contract: `VG.Spec.ChaCha20.blockContract`. Constant time: only the pointers may affect \
    timing, not the state."
  safety := [
    "On return the first 64 bytes of `buf` hold the result and the rest is unspecified."]

/-- `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`.
`state` is left unspecified, and `buf` is working space: 64 bytes more than
`vg_chacha20_block`'s, so that an implementation that calls it can keep what
it must preserve across the call (e.g. its caller's callee-saved registers)
in `buf` outside the part it passes to the block function. -/
def xorSig : Sig where
  params := [("state", .array true .u32 16), ("data", .slice true .u8 "len"),
    ("buf", .array true .u32 80)]

/-- XORs the first `len` bytes of the keystream of the state at `state` into
the `len` bytes at `data`. The state (key, counter and nonce) and the data
are secret. -/
def xorContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  xorSig.contract A (post := fun state data len _buf m m' _ =>
    bytesAt m' data len.toNat =
      List.zipWith (· ^^^ ·) (bytesAt m data len.toNat) (keystream (stateAt m state) len.toNat))
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_xor` on every target. -/
def xorApi : Api where
  module := "chacha20"
  name := "vg_chacha20_xor"
  sig := xorSig
  writeArgs := true
  contracts := some fun A stack => xorContract A stack
  summary := "XORs the first `len` bytes of the ChaCha20 keystream of the 16-word state `*state` \
    (RFC 8439 §2.4: the block function of the state with its block counter, word 12, advanced by \
    0, 1, … modulo 2³²) into the `len` bytes at `data`, calling `vg_chacha20_block` for each 64 \
    bytes.\n\n\
    Contract: `VG.Spec.ChaCha20.xorContract`. Constant time: only the pointers and `len` may \
    affect timing, not the state or the data."
  safety := [
    "The contents of `state` on return are unspecified.",
    "The contents of `buf` on return are unspecified."]

/-- `vg_chacha20_init(state: *mut [u64; 96], key: *const [u8; 32], nonce: *const [u8; 16])`. -/
def initSig : Sig where
  params := [("state", .array true .u64 96), ("key", .array false .u8 32),
    ("nonce", .array false .u8 16)]

/-- Makes the streaming state at `state` hold the 32-byte key at `key` and
represent its whole keystream for the 16-byte nonce at `nonce`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (post := fun state key nonce m m' _ =>
    keyAt m' state = bytesAt m key 32 ∧
      restAt m' state = keystreamOf (bytesAt m key 32) (bytesAt m nonce 16))
    (stack := stack)

/-- `vg_chacha20_init` on every target. -/
def initApi : Api where
  module := "chacha20"
  name := "vg_chacha20_init"
  sig := initSig
  contracts := some fun A stack => initContract A stack
  summary := "Starts a ChaCha20 keystream (RFC 8439 §2.4): makes the streaming state `*state` hold \
    the 32-byte key `*key` and the whole keystream for the 16-byte nonce `*nonce`, the initial \
    block counter `c` (4 bytes, little-endian) followed by the 12-byte RFC 8439 nonce: the blocks \
    for the counters `c` to 2³² − 1, 64 × (2³² − `c`) bytes.\n\n\
    Contract: `VG.Spec.ChaCha20.initContract`. The streaming state is opaque \
    (`VG.Spec.ChaCha20.keyAt`, `VG.Spec.ChaCha20.restAt`). Constant time: only the pointers may \
    affect timing, not the key or the nonce."
  safety := []

/-- `vg_chacha20_set_nonce(state: *mut [u64; 96], nonce: *const [u8; 16])`. -/
def setNonceSig : Sig where
  params := [("state", .array true .u64 96), ("nonce", .array false .u8 16)]

/-- Keeps the key of the streaming state at `state`, and makes it represent
the whole keystream of that key for the 16-byte nonce at `nonce`. -/
def setNonceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  setNonceSig.contract A (post := fun state nonce m m' _ =>
    keyAt m' state = keyAt m state ∧
      restAt m' state = keystreamOf (keyAt m state) (bytesAt m nonce 16))
    (stack := stack)

/-- `vg_chacha20_set_nonce` on every target. -/
def setNonceApi : Api where
  module := "chacha20"
  name := "vg_chacha20_set_nonce"
  sig := setNonceSig
  contracts := some fun A stack => setNonceContract A stack
  summary := "Restarts a ChaCha20 keystream with the same key: makes the streaming state `*state` \
    represent the whole keystream of its key for the 16-byte nonce `*nonce` (as \
    `vg_chacha20_init` does), discarding what was left of the previous one.\n\n\
    Contract: `VG.Spec.ChaCha20.setNonceContract`. Constant time: only the pointers may affect \
    timing, not the key or the nonce."
  safety := []

/-- `vg_chacha20_apply(state: *mut [u64; 96], data: *mut u8, len: usize) -> u32`. -/
def applySig : Sig where
  params := [("state", .array true .u64 96), ("data", .slice true .u8 "len")]
  ret := some .u32

/-- If at least `len` bytes of keystream are left in the streaming state at
`state`, XORs the next `len` of them into the `len` bytes at `data`, leaves
the rest in the state, and returns 1. Otherwise returns 0, leaving the data
and what the state represents unchanged. The key is kept either way. May
leak the number of bytes of keystream left. -/
def applyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  applySig.contract A (post := fun state data len m m' r =>
    keyAt m' state = keyAt m state ∧
      if len.toNat ≤ leftAt m state then
        r = 1 ∧
          bytesAt m' data len.toNat =
            List.zipWith (· ^^^ ·) (bytesAt m data len.toNat) ((restAt m state).take len.toNat) ∧
          restAt m' state = (restAt m state).drop len.toNat
      else
        r = 0 ∧ bytesAt m' data len.toNat = bytesAt m data len.toNat ∧
          restAt m' state = restAt m state)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun state _data _len m => [leftAt m state])

/-- `vg_chacha20_apply` on every target. -/
def applyApi : Api where
  module := "chacha20"
  name := "vg_chacha20_apply"
  sig := applySig
  writeArgs := true
  contracts := some fun A stack => applyContract A stack
  summary := "Applies a ChaCha20 keystream (RFC 8439 §2.4), encrypting or decrypting: if at least \
    `len` bytes are left of the keystream that the streaming state `*state` represents, XORs the \
    next `len` of them into the `len` bytes at `data`, keeps the rest in `*state`, and returns 1. \
    Otherwise (the block counter would pass 2³² − 1) returns 0, and leaves the bytes at `data` \
    and the keystream unchanged.\n\n\
    Contract: `VG.Spec.ChaCha20.applyContract`. Constant time: only the pointers, `len` and the \
    number of bytes of keystream left in `*state` (`VG.Spec.ChaCha20.leftAt`: 64 × (2³² − `c`) \
    for the initial block counter `c`, less the bytes applied since) may affect timing, not the \
    key, the nonce, the keystream or the data. The function may leak that number."
  safety := []

end VG.Spec.ChaCha20
