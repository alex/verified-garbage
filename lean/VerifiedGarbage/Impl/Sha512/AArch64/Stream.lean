import VerifiedGarbage.Impl.Sha512.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming SHA-512: AArch64 implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`).

* `init iv (state = x0)` stores the initial hash value `iv`.
* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)` and
  `finalize(state = x0, count = x1, out = x2, scratch = x3)` are the generic
  streaming code of `Impl/MdStream/AArch64.lean`, calling the compression
  function with the suffix `suffix` (`vg_sha512_compress` or
  `vg_sha512_compress_sha3`, `compressName`), and are emitted once for each
  implementation (`Generic/MdHash/AArch64/Stream.lean`). It is called with
  `scratch[0..scratchBytes)` as its scratch space; our caller's callee-saved
  registers are saved in the 48 bytes after it. The length field is the length in bits as
  a 128-bit big-endian integer: `count >> 61`, then `count << 3` (modulo
  2⁶⁴); the words of the final hash value are big-endian.
-/

namespace VG.Impl.Sha512.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha512.AArch64 (movImm64 scratchBytes)
open VG.Impl.MdStream.AArch64 (Params len128 out64)

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => movImm64 .x9 iv[k]! ++ [.str .x .x9 .x0 (8 * k)])

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := scratchBytes
  -- The length field, at `N + B - L`.
  len := len128 176
  out := out64 8

/-- The symbol of the compression function with the suffix `suffix`. -/
def compressName (suffix : String) : String := "vg_sha512_compress" ++ suffix

/-- `update`, calling the compression function `code` with the suffix `suffix`. -/
def updateWith (suffix : String) (code : Prog isa) : Prog isa :=
  MdStream.AArch64.update params (compressName suffix) code

/-- `finalize`, calling the compression function `code` with the suffix `suffix`. -/
def finalizeWith (suffix : String) (code : Prog isa) : Prog isa :=
  MdStream.AArch64.finalize params (compressName suffix) code

end VG.Impl.Sha512.AArch64.Stream
