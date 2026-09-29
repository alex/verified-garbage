import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.Artifact

/-!
# Poly1305: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming Poly1305
(`init`/`update`/`finalize` and `blocks`, on the representations `Buffered`
and `Repr`), in terms of `Spec/Poly1305.lean`, for any target: `A` is the
target's calling convention. The signatures fix where the arguments are, the
memory each function may access, disjointness, and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contracts add the rest. The key,
the accumulator and the message are secret; the message's length so far
(`count`) is public, as the lengths of its pieces are.

`vg_poly1305_init` stores the key and a zero accumulator (the empty message,
which `Repr` and `Buffered` both describe). `vg_poly1305_update` absorbs
bytes of any length, buffering in the state the ones that do not fill a
block, and `vg_poly1305_finalize` absorbs the buffered bytes and computes the
tag, as the hashes' `update` and `finalize` do; like theirs, they take 128
bytes of working space (`scratch`), since the state's own working space
(bytes 72–127) is too small for some targets. `vg_poly1305_blocks` absorbs
whole blocks into the state of a message of whole blocks, for callers that
pad their message themselves (e.g. ChaCha20-Poly1305).

`finalizeTailContract` is the previous `finalize`, which absorbs the
message's last bytes from the caller: it stays until the implementations have
moved to `updateContract` and `finalizeContract`.

Each contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none.
-/

namespace VG.Spec.Poly1305

/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initSig : Sig where
  params := [("state", .array true .u64 16), ("key", .array false .u8 32)]

/-- Makes the state at `state` represent the empty message under the 32-byte
one-time key at `key`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (post := fun state key m m' _ => Repr m' state (bytesAt m key 32) [])
    (stack := stack)

/-- `vg_poly1305_init` on every target. -/
def initApi : Api where
  module := "poly1305"
  name := "vg_poly1305_init"
  sig := initSig
  summary := "Starts a Poly1305 computation (RFC 8439 §2.5): makes the streaming state `*state` \
    represent the empty message under the 32-byte one-time key `*key`.\n\n\
    Contract: `VG.Spec.Poly1305.initContract`. The streaming state is the accumulator followed by \
    the key (`VG.Spec.Poly1305.Repr`). Constant time: only the pointers may affect timing, not the \
    key."
  safety := [
    "`state` must be valid for writes of 128 bytes.",
    "`key` must be valid for reads of 32 bytes."]

/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksSig : Sig where
  params := [("state", .array true .u64 16), ("blocks", .slice false (.array .u8 16) "n")]

/-- If the state at `state` represents a message `msg` under a key, then
afterwards it represents `msg` followed by the `n` 16-byte blocks at
`blocks`, under the same key. -/
def blocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A (post := fun state blocks n m m' _ =>
    ∀ key msg, Repr m state key msg → Repr m' state key (msg ++ bytesAt m blocks (16 * n.toNat)))
    (stack := stack)

/-- `vg_poly1305_blocks` on every target. -/
def blocksApi : Api where
  module := "poly1305"
  name := "vg_poly1305_blocks"
  sig := blocksSig
  summary := "Absorbs whole blocks into a Poly1305 computation: if the streaming state `*state` \
    represents a message under a key, it then represents that message followed by the `n` 16-byte \
    blocks at `blocks`, under the same key.\n\n\
    Contract: `VG.Spec.Poly1305.blocksContract`. Constant time: only the pointers and `n` may \
    affect timing, not the state or the data."
  safety := [
    "`state` must be valid for reads and writes of 128 bytes.",
    "`blocks` must be valid for reads of `16 * n` bytes."]

/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 16])`.
`count` is public; `scratch` is working space. -/
def updateSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 16)]

/-- If the state at `state` represents a message `msg` of `count` bytes
(modulo 2⁶⁴) under a key, with its last bytes buffered, then afterwards it
represents `msg` followed by the `len` bytes at `data`, under the same key. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ key msg, Buffered m state key msg → count = BitVec.ofNat 64 msg.length →
      Buffered m' state key (msg ++ bytesAt m data len.toNat))
    (stack := stack)

/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 16])`.
`count` is public; `state` is left unspecified, and `scratch` is working
space. -/
def finalizeSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("out", .array true .u8 16), ("scratch", .array true .u64 16)]

/-- If the state at `state` represents a message `msg` of `count` bytes
(modulo 2⁶⁴) under a key, with its last bytes buffered, writes the Poly1305
tag of `msg` under that key to `out`. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out _scratch m m' _ =>
    ∀ key msg, Buffered m state key msg → count = BitVec.ofNat 64 msg.length →
      bytesAt m' out 16 = mac key msg)
    (stack := stack)

/-- The previous `vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16])`.
`state` is left unspecified. -/
def finalizeTailSig : Sig where
  params := [("state", .array true .u64 16), ("tail", .slice false .u8 "len"),
    ("out", .array true .u8 16)]

/-- For `len` less than 16: if the state at `state` represents a message
`msg` under a key, writes the Poly1305 tag of `msg` followed by the `len`
bytes at `tail`, under that key, to `out`. -/
def finalizeTailContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeTailSig.contract A
    (pre := fun _state _tail len _out _ => len.toNat < 16)
    (post := fun state tail len out m m' _ =>
      ∀ key msg, Repr m state key msg → bytesAt m' out 16 = mac key (msg ++ bytesAt m tail len.toNat))
    (stack := stack)

/-- `vg_poly1305_finalize` on every target. -/
def finalizeTailApi : Api where
  module := "poly1305"
  name := "vg_poly1305_finalize"
  sig := finalizeTailSig
  summary := "Finishes a Poly1305 computation: if the streaming state `*state` represents a \
    message under a key, writes the tag of that message followed by the `len` bytes at `tail`, \
    under that key, to `*out`.\n\n\
    Contract: `VG.Spec.Poly1305.finalizeTailContract`. Constant time: only the pointers and `len` \
    may affect timing, not the state or the data."
  safety := [
    "`len` must be less than 16.",
    "`state` must be valid for reads and writes of 128 bytes; its contents on return are \
      unspecified.",
    "`tail` must be valid for reads of `len` bytes.",
    "`out` must be valid for writes of 16 bytes."]

end VG.Spec.Poly1305
