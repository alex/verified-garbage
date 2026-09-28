import VerifiedGarbage.Impl.Sha512.X86_64

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

The compression function's code (`Impl.Sha512.X86_64.compress`) is inlined
with `scratch` as its scratch space; it saves and restores `rbx, rbp,
r12–r15`, so our own variables live there across it (`rbx` = `state`, `r15` =
`scratch`), and our caller's values of those registers are saved in
`scratch[176..224)`. Every address and branch depends only on the pointers,
`count` and `len`.
-/

namespace VG.Impl.Sha512.X86_64.Stream

open VG.X86_64
open VG.Impl.Sha512.X86_64 (at_ compress)

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => [.movImm64 .rax iv[k]!, .store (at_ .rdi (8 * k)) .rax])

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.rbx, 176), (.rbp, 184), (.r12, 192), (.r13, 200), (.r14, 208), (.r15, 216)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- `[rbx + r13 + 64]`: byte `r` of the buffer. -/
def bufByte : MemOp := { base := .rbx, index := some .r13, scale := 1, disp := 64 }

/-- Compress the block at `rsi` into the hash value at `rbx`, with scratch
space `r15`. -/
def compressAt : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)])
    (.seq compress (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)]))

/-! ## `update`

Registers: `rbp` = `data`, `r12` = bytes of `data` left, `r13` = bytes in the
buffer, `r14` = whether this iteration compresses a block. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [.mov .rsi (.reg .rbp), .alu .add .rbp (.imm 128), .alu .sub .r12 (.imm 128), .mov32 .r14 (.imm 1)]

/-- Copy `min(128 - r13, r12)` bytes of `data` into the buffer; if that fills
it, compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 128), .alu .sub .rax (.reg .r13), .alu .cmp .r12 (.reg .rax)])
  (.seq (.ite .b (.block [.mov .rax (.reg .r12)]) (.block []))
  (.seq (.block [.alu .sub .r12 (.reg .rax), .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movzx8 .r9 { base := .rbp }, .store8 bufByte .r9,
        .alu .add .rbp (.imm 1), .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne))
  (.seq (.block [.mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 128)])
    (.ite .e (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64), .mov32 .r13 (.imm 0),
        .mov32 .r14 (.imm 1)]) (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.alu .test .r13 (.reg .r13)])
  (.seq (.ite .e (.seq (.block [.alu .cmp .r12 (.imm 128)]) (.ite .ae (.block direct) fill)) fill)
  (.seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .ne compressAt (.block []))
    (.block [.alu .test .r14 (.reg .r14)]))))

def update : Prog isa :=
  .seq (.block (save .r8 ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .r8), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rcx), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 127)]))
    (.seq (.loop updateBody .ne) (.block restore))

/-! ## `finalize`

Registers: `rbp` = `out`, `r12` = `count`, `r13` = bytes in the buffer,
`r14` = 1 while the block being padded is not the last one. -/

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r13` to 128, or to 112 in the last block.
  .seq (.block [.mov32 .rax (.imm 128), .alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block [.mov32 .rax (.imm 112)]) (.block []))
  (.seq (.block [.mov32 .r9 (.imm 0), .alu .sub .rax (.reg .r13)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.store8 bufByte .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne))
  -- In the last block, the message length in bits as a 128-bit big-endian
  -- integer: `count >> 61`, then `count << 3` (modulo 2⁶⁴).
  (.seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block [.mov .rax (.reg .r12), .shift .shr .rax 61, .bswap .rax,
      .store (at_ .rbx 176) .rax,
      .mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .rbx 184) .rax]) (.block []))
  (.seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64)])
  (.seq compressAt
    (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]))))))))

def finalize : Prog isa :=
  .seq (.block (save .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 127),
      -- The `0x80` byte.
      .mov32 .rax (.imm 0x80), .store8 bufByte .rax, .alu .add .r13 (.imm 1),
      -- Two blocks if it leaves fewer than 16 bytes for the length.
      .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 113)]))
  (.seq (.ite .ae (.block [.mov32 .r14 (.imm 1)]) (.block []))
  (.seq (.loop finalizeBody .e)
    (.block ((List.range 8).flatMap (fun k =>
        [.mov .rax (.mem (at_ .rbx (8 * k))), .bswap .rax, .store (at_ .rbp (8 * k)) .rax]) ++
      restore))))

end VG.Impl.Sha512.X86_64.Stream
