import VerifiedGarbage.Impl.Md5.X86
import VerifiedGarbage.Impl.MdStream.X86

/-!
# Streaming MD5: x86 (32-bit) implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`). Every argument is on the stack
(cdecl).

* `init(state)` stores the initial MD buffer.
* `update(state, count, data, len, scratch)` and
  `finalize(state, count, out, scratch)` are the generic streaming code of
  `Impl/MdStream/X86.lean`, calling `vg_md5_compress`
  (`Impl.Md5.X86.compress`) with `scratch[0..64)` as its scratch space; our
  caller's callee-saved registers are saved in `scratch[64..80)`, and
  `finalize` keeps `count` and `out` in `scratch[80..92)`. The length field is
  little-endian, and so are the words of the digest.
-/

namespace VG.Impl.Md5.X86.Stream

open VG.X86
open VG.Impl.Md5.X86 (at_ compress)
open VG.Impl.MdStream.X86 (Params len64 out32)

def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block ((List.range 4).flatMap fun k =>
      [.mov .ecx (.imm Spec.Md5.H0[k]!), .store (at_ .eax (4 * k)) .ecx]))

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := len64 64 72 false
  out := out32 4 false

def update : Prog isa := MdStream.X86.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.X86.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.X86.Stream
