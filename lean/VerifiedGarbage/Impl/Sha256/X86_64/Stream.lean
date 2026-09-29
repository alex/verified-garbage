import VerifiedGarbage.Impl.Sha256.X86_64
import VerifiedGarbage.Impl.Sha256.X86_64.ShaNi
import VerifiedGarbage.Impl.Sha256.X86_64.Avx2
import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# Streaming SHA-256: x86-64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = rdi)` stores `H⁽⁰⁾`.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

`update` and `finalize` are the generic streaming code of
`Impl/MdStream/X86_64.lean`. They take the compression function they call (a
`Callee`, e.g. `vg_sha256_compress` or `vg_sha256_compress_shani`), and are
emitted once for each implementation
(`Generic/Sha256Compress/X86_64/Sha256.lean`). It is called with
`scratch[0..560)` as its scratch space; our caller's callee-saved registers
are saved in `scratch[560..608)`. The length field is big-endian, and so are
the words of the digest. (HMAC-SHA256 calls the compression function and
saves registers the same way: `saved`, `save`, `restore` and `compressAt`.)
-/

namespace VG.Impl.Sha256.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_ compress)

/-- A compression function to call: its symbol and its code. -/
structure Callee where
  name : String
  code : Prog isa

def Callee.scalar : Callee := ⟨"vg_sha256_compress", compress⟩
def Callee.shani : Callee := ⟨"vg_sha256_compress_shani", ShaNi.compress⟩
def Callee.avx2 : Callee := ⟨"vg_sha256_compress_avx2", Avx2.compress⟩

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.mov32 .rax (.imm Spec.Sha256.H0[k]!), .store32 (at_ .rdi (4 * k)) .rax])

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.rbx, 560), (.rbp, 568), (.r12, 576), (.r13, 584), (.r14, 592), (.r15, 600)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- Compress the block at `rsi` into the hash value at `rbx`, with scratch
space `r15`. (`rbx` and `r15` are copied back from `rdi` and `rcx`, which
the compression function keeps, only for the constant-time analysis, which
tracks which registers hold the base address of a region through registers
but not through memory.) -/
def compressAt (f : Callee) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)])
    (.seq (.call f.name f.code) (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)]))

/-- The sizes, the length field and the digest. -/
def params : MdStream.X86_64.Params where
  N := 32
  B := 64
  L := 8
  so := 560
  len := MdStream.X86_64.len64 88 true
  out := MdStream.X86_64.out32 8 true

def update (f : Callee) : Prog isa := MdStream.X86_64.update params f.name f.code

def finalize (f : Callee) : Prog isa := MdStream.X86_64.finalize params f.name f.code

end VG.Impl.Sha256.X86_64.Stream
