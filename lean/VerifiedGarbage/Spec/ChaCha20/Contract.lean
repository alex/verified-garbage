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
  summary := "The ChaCha20 block function (RFC 8439 §2.3): writes the block function of the \
    16-word state `*state` (20 rounds, then the input state added word by word) to the first 16 \
    words of `*buf`.\n\n\
    Contract: `VG.Spec.ChaCha20.blockContract`. Constant time: only the pointers may affect \
    timing, not the state."
  safety := [
    "`state` must be valid for reads of 64 bytes.",
    "`buf` must be valid for reads and writes of 256 bytes. On return its first 64 bytes hold the \
      result and the rest is unspecified."]

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

end VG.Spec.ChaCha20
