import VerifiedGarbage.Impl.Sha1.X86_64
import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming SHA-1: x86-64 implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = rdi)` stores `H⁽⁰⁾`.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`, calling `vg_sha1_compress`
(`Impl.Sha1.X86_64.compress`) with `scratch[0..112)` as its scratch space;
our caller's callee-saved registers are saved in `scratch[112..160)`. The
length field is big-endian, and so are the words of the digest.
-/

namespace VG.Impl.Sha1.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha1.X86_64 (at_ compress)
open VG.Impl.MdStream.X86_64 (Params len64 out32)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.mov32 .rax (.imm Spec.Sha1.H0[k]!), .store32 (at_ .rdi (4 * k)) .rax])

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := len64 76 true
  out := out32 5 true

def update : Prog isa := MdStream.X86_64.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.X86_64.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.X86_64.Stream
