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
tag, as the hashes' `update` and `finalize` do. `vg_poly1305_blocks` absorbs
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

/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the state at `state` represents a message `msg` of `count` bytes
(modulo 2⁶⁴) under a key, with its last bytes buffered, then afterwards it
represents `msg` followed by the `len` bytes at `data`, under the same key. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len m m' _ =>
    ∀ key msg, Buffered m state key msg → count = BitVec.ofNat 64 msg.length →
      Buffered m' state key (msg ++ bytesAt m data len.toNat))
    (stack := stack)

/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16])`.
`count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("out", .array true .u8 16)]

/-- If the state at `state` represents a message `msg` of `count` bytes
(modulo 2⁶⁴) under a key, with its last bytes buffered, writes the Poly1305
tag of `msg` under that key to `out`. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := fun state count out m m' _ =>
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

end VG.Spec.Poly1305
