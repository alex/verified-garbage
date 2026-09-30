import VerifiedGarbage.Impl.Sha512.X86_64
import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming SHA-512: x86-64 implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`).

* `init iv (state = rdi)` stores the initial hash value `iv`.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the final
  hash value.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`. They take the compression function they call (a
`Callee`, e.g. `vg_sha512_compress`), and are emitted once for each
implementation (`Generic/Sha512Compress/X86_64/Sha512.lean`). It is called
with `scratch[0..176)` as its scratch space; our caller's callee-saved
registers are saved in `scratch[176..224)`. The
length field is the length in bits as a 128-bit big-endian integer:
`count >> 61`, then `count << 3` (modulo 2⁶⁴); the words of the final hash
value are big-endian.
-/

namespace VG.Impl.Sha512.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha512.X86_64 (at_ compress)
open VG.Impl.MdStream.X86_64 (Params len64 out64)

/-- A compression function to call: its symbol and its code. -/
structure Callee where
  name : String
  code : Prog isa

def Callee.scalar : Callee := ⟨"vg_sha512_compress", compress⟩

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => [.movImm64 .rax iv[k]!, .store (at_ .rdi (8 * k)) .rax])

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := 176
  len := [.mov .rax (.reg .r12), .shift .shr .rax 61, .bswap .rax, .store (at_ .rbx 176) .rax] ++
    len64 184 true
  out := out64 8

def update (f : Callee) : Prog isa := MdStream.X86_64.update params f.name f.code

def finalize (f : Callee) : Prog isa := MdStream.X86_64.finalize params f.name f.code

end VG.Impl.Sha512.X86_64.Stream
