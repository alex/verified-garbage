import VerifiedGarbage.Impl.Md5.X86_64
import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming MD5: x86-64 implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = rdi)` stores the initial MD buffer.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`, calling `vg_md5_compress`
(`Impl.Md5.X86_64.compress`) with `scratch[0..64)` as its scratch space; our
caller's callee-saved registers are saved in `scratch[64..112)`. The length
field is little-endian, and so are the words of the digest.
-/

namespace VG.Impl.Md5.X86_64.Stream

open VG.X86_64
open VG.Impl.Md5.X86_64 (at_ compress)
open VG.Impl.MdStream.X86_64 (Params len64 out32)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.mov32 .rax (.imm Spec.Md5.H0[k]!), .store32 (at_ .rdi (4 * k)) .rax])

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := len64 72 false
  out := out32 4 false

def update : Prog isa := MdStream.X86_64.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.X86_64.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.X86_64.Stream
