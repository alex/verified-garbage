import VerifiedGarbage.Impl.Sha1.X86
import VerifiedGarbage.Impl.MdStream.X86

/-!
# Streaming SHA-1: x86 (32-bit) implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`). Every argument is on the stack
(cdecl).

* `init(state)` stores the initial hash value.
* `update(state, count, data, len, scratch)` and
  `finalize(state, count, out, scratch)` are the generic streaming code of
  `Impl/MdStream/X86.lean`, calling `vg_sha1_compress`
  (`Impl.Sha1.X86.compress`) with `scratch[0..112)` as its scratch space;
  our caller's callee-saved registers are saved in `scratch[112..128)`, and
  `finalize` keeps `count` and `out` in `scratch[128..140)`. The length field
  is big-endian, and so are the words of the digest.
-/

namespace VG.Impl.Sha1.X86.Stream

open VG.X86
open VG.Impl.Sha1.X86 (at_ compress)
open VG.Impl.MdStream.X86 (Params len64 out32)

def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block ((List.range 5).flatMap fun k =>
      [.mov .ecx (.imm Spec.Sha1.H0[k]!), .store (at_ .eax (4 * k)) .ecx]))

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := len64 112 76 true
  out := out32 5 true

def update : Prog isa := MdStream.X86.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.X86.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.X86.Stream
