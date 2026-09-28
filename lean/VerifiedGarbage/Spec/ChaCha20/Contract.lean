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

/-- `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 64])`.
`state` is left unspecified, and `buf` is working space. -/
def xorSig : Sig where
  params := [("state", .array true .u32 16), ("data", .slice true .u8 "len"),
    ("buf", .array true .u32 64)]

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
