import VerifiedGarbage.Impl.Md5.X86_64

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

The compression function is called (`vg_md5_compress`,
`Impl.Md5.X86_64.compress`) with `scratch` as its scratch space; it preserves
`rbx, rbp, r12–r15`, so our own variables live there across it (`rbx` =
`state`, `r15` = `scratch`), and our caller's values of those registers are
saved in `scratch[64..112)`. The call stores its return address in the 8
bytes below `rsp`. Every address and branch depends only on the pointers,
`count` and `len`.
-/

namespace VG.Impl.Md5.X86_64.Stream

open VG.X86_64
open VG.Impl.Md5.X86_64 (at_ compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.mov32 .rax (.imm Spec.Md5.H0[k]!), .store32 (at_ .rdi (4 * k)) .rax])

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.rbx, 64), (.rbp, 72), (.r12, 80), (.r13, 88), (.r14, 96), (.r15, 104)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- `[rbx + r13 + 16]`: byte `r` of the buffer. -/
def bufByte : MemOp := { base := .rbx, index := some .r13, scale := 1, disp := 16 }

/-- Compress the block at `rsi` into the MD buffer at `rbx`, with scratch
space `r15`. (`rbx` and `r15` are copied back from `rdi` and `rcx`, which
the compression function keeps, only for the constant-time analysis, which
tracks which registers hold the base address of a region through registers
but not through memory.) -/
def compressAt : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)])
    (.seq (.call "vg_md5_compress" compress) (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)]))

/-! ## `update`

Registers: `rbp` = `data`, `r12` = bytes of `data` left, `r13` = bytes in the
buffer, `r14` = whether this iteration compresses a block. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [.mov .rsi (.reg .rbp), .alu .add .rbp (.imm 64), .alu .sub .r12 (.imm 64), .mov32 .r14 (.imm 1)]

/-- Copy `min(64 - r13, r12)` bytes of `data` into the buffer; if that fills it,
compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 64), .alu .sub .rax (.reg .r13), .alu .cmp .r12 (.reg .rax)])
  (.seq (.ite .b (.block [.mov .rax (.reg .r12)]) (.block []))
  (.seq (.block [.alu .sub .r12 (.reg .rax), .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movzx8 .r9 { base := .rbp }, .store8 bufByte .r9,
        .alu .add .rbp (.imm 1), .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne))
  (.seq (.block [.mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 64)])
    (.ite .e (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 16), .mov32 .r13 (.imm 0),
        .mov32 .r14 (.imm 1)]) (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.alu .test .r13 (.reg .r13)])
  (.seq (.ite .e (.seq (.block [.alu .cmp .r12 (.imm 64)]) (.ite .ae (.block direct) fill)) fill)
  (.seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .ne compressAt (.block []))
    (.block [.alu .test .r14 (.reg .r14)]))))

def update : Prog isa :=
  .seq (.block (save .r8 ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .r8), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rcx), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 63)]))
    (.seq (.loop updateBody .ne) (.block restore))

/-! ## `finalize`

Registers: `rbp` = `out`, `r12` = `count`, `r13` = bytes in the buffer,
`r14` = 1 while the block being padded is not the last one. -/

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r13` to 64, or to 56 in the last block.
  .seq (.block [.mov32 .rax (.imm 64), .alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block [.mov32 .rax (.imm 56)]) (.block []))
  (.seq (.block [.mov32 .r9 (.imm 0), .alu .sub .rax (.reg .r13)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.store8 bufByte .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne))
  -- In the last block, the message length in bits, little-endian.
  (.seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .store (at_ .rbx 72) .rax]) (.block []))
  (.seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 16)])
  (.seq compressAt
    (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]))))))))

def finalize : Prog isa :=
  .seq (.block (save .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 63),
      -- The `0x80` byte.
      .mov32 .rax (.imm 0x80), .store8 bufByte .rax, .alu .add .r13 (.imm 1),
      -- Two blocks if it leaves fewer than 8 bytes for the length.
      .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 57)]))
  (.seq (.ite .ae (.block [.mov32 .r14 (.imm 1)]) (.block []))
  (.seq (.loop finalizeBody .e)
    (.block ((List.range 4).flatMap (fun k =>
        [.mov32 .rax (.mem (at_ .rbx (4 * k))), .store32 (at_ .rbp (4 * k)) .rax]) ++
      restore))))

end VG.Impl.Md5.X86_64.Stream
