import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Streaming Merkle–Damgård hash functions: x86-64 implementation

The streaming `update` and `finalize` of MD5, SHA-1, SHA-256 and the SHA-512
family, which differ only in their sizes, in how they store the message
length and output the digest, and in the compression function they call
(`Params`). Each hash function's `Impl/<Alg>/X86_64/Stream.lean` instantiates
them.

The streaming state (`N + B` bytes at `state`) is the hash value (`N` bytes)
followed by a `B`-byte buffer.

* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  processes one block per iteration: straight from `data` while the buffer is
  empty and a whole block remains, otherwise by copying bytes into the buffer,
  compressing it once it is full.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

The compression function (`name`, `code`) is called with `scratch` as its
scratch space; it preserves `rbx, rbp, r12–r15`, so our own variables live
there across it (`rbx` = `state`, `r15` = `scratch`), and our caller's values
of those registers are saved in `scratch[so..so+48)`. The call stores its
return address in the 8 bytes below `rsp`. Every address and branch depends
only on the pointers, `count` and `len`.
-/

namespace VG.Impl.MdStream.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- The block size. -/
  B : Nat
  /-- The size of the length field at the end of the last block. -/
  L : Nat
  /-- Where our caller's registers are saved in the scratch space, after the
  compression function's own. -/
  so : Nat
  /-- Stores the length field, from `count` in `r12`, at `rbx + N + B - L`;
  writes only `rax` (and the flags). -/
  len : List Instr
  /-- Writes the digest, from the hash value at `rbx`, to `rbp`; writes only
  `rax` (and the flags). -/
  out : List Instr

variable (P : Params)

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.rbx, P.so), (.rbp, P.so + 8), (.r12, P.so + 16), (.r13, P.so + 24), (.r14, P.so + 32), (.r15, P.so + 40)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := (saved P).map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := (saved P).map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- `[rbx + r13 + N]`: byte `r13` of the buffer. -/
def bufByte : MemOp := { base := .rbx, index := some .r13, scale := 1, disp := P.N }

/-- Compress the block at `rsi` into the hash value at `rbx`, with scratch
space `r15`, by calling the compression function `name` (whose code is
`code`). (`rbx` and `r15` are copied back from `rdi` and `rcx`, which the
compression function keeps, only for the constant-time analysis, which
tracks which registers hold the base address of a region through registers
but not through memory.) -/
def compressAt (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)])
    (.seq (.call name code) (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)]))

/-! ## `update`

Registers: `rbp` = `data`, `r12` = bytes of `data` left, `r13` = bytes in the
buffer, `r14` = whether this iteration compresses a block. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [.mov .rsi (.reg .rbp), .alu .add .rbp (.imm (BitVec.ofNat 32 P.B)),
    .alu .sub .r12 (.imm (BitVec.ofNat 32 P.B)), .mov32 .r14 (.imm 1)]

/-- The loop copying bytes of `data` into the buffer. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .r9 { base := .rbp }, .store8 (bufByte P) .r9,
    .alu .add .rbp (.imm 1), .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne

/-- Copy `min(B - r13, r12)` bytes of `data` into the buffer; if that fills it,
compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 P.B)), .alu .sub .rax (.reg .r13), .alu .cmp .r12 (.reg .rax)])
  (.seq (.ite .b (.block [.mov .rax (.reg .r12)]) (.block []))
  (.seq (.block [.alu .sub .r12 (.reg .rax), .alu .test .rax (.reg .rax)])
  (.seq (.ite .e (.block []) (copyLoop P))
  (.seq (.block [.mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm (BitVec.ofNat 32 P.B))])
    (.ite .e (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N)), .mov32 .r13 (.imm 0),
        .mov32 .r14 (.imm 1)]) (.block []))))))

/-- The first half of an iteration: the next block, if any, is ready at `rsi`
(`r14` = 1), or all the data is buffered (`r14` = 0). -/
def updateHead : Prog isa :=
  .seq (.block [.alu .test .r13 (.reg .r13)])
    (.ite .e (.seq (.block [.alu .cmp .r12 (.imm (BitVec.ofNat 32 P.B))]) (.ite .ae (.block (direct P)) (fill P)))
      (fill P))

/-- The second half: compress the block if there is one, and loop back if so. -/
def updateTail (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .ne (compressAt name code) (.block []))
    (.block [.alu .test .r14 (.reg .r14)]))

def updateBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (updateHead P) (updateTail name code)

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save P .r8 ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .r8), .mov .rbp (.reg .rdx),
    .mov .r12 (.reg .rcx), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm (BitVec.ofNat 32 (P.B - 1)))]

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (updateStart P)) (.seq (.loop (updateBody P name code) .ne) (.block (restore P)))

/-! ## `finalize`

Registers: `rbp` = `out`, `r12` = `count`, `r13` = bytes in the buffer,
`r14` = 1 while the block being padded is not the last one. -/

/-- The loop zeroing the buffer from `r13` on, `rax` bytes. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (bufByte P) .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne

/-- Pad the block, up to the call of the compression function. -/
def finalizePad : Prog isa :=
  -- Zero the buffer from `r13` to `B`, or to `B - L` in the last block.
  .seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 P.B)), .alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (P.B - P.L)))]) (.block []))
  (.seq (.block [.mov32 .r9 (.imm 0), .alu .sub .rax (.reg .r13)])
  (.seq (.ite .e (.block []) (zeroLoop P))
  -- In the last block, the length field.
  (.seq (.block [.alu .test .r14 (.reg .r14)])
  (.seq (.ite .e (.block P.len) (.block []))
    (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N))]))))))

def finalizeBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (finalizePad P)
  (.seq (compressAt name code)
    (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]))

/-- Save registers, append the `0x80` byte and choose the number of blocks. -/
def finalizeStart : Prog isa :=
  .seq (.block (save P .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm (BitVec.ofNat 32 (P.B - 1))),
      -- The `0x80` byte.
      .mov32 .rax (.imm 0x80), .store8 (bufByte P) .rax, .alu .add .r13 (.imm 1),
      -- Two blocks if it leaves fewer than `L` bytes for the length.
      .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (P.B - P.L + 1)))]))
    (.ite .ae (.block [.mov32 .r14 (.imm 1)]) (.block []))

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (finalizeStart P)
  (.seq (.loop (finalizeBody P name code) .e)
    (.block (P.out ++ restore P)))

/-! ## Length fields and digests

The `len` and `out` of the hash functions here. -/

/-- The length in bits, `8 · count` (modulo 2⁶⁴, from `count` in `r12`), as 8
bytes at `rbx + d`, big-endian if `be` and little-endian otherwise. -/
def len64 (d : Nat) (be : Bool) : List Instr :=
  [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)] ++
    (if be then [.bswap .rax] else []) ++ [.store (at_ .rbx d) .rax]

/-- The `n` 32-bit words at `rbx`, written to `rbp`, big-endian if `be` and
little-endian otherwise. -/
def out32 (n : Nat) (be : Bool) : List Instr :=
  (List.range n).flatMap fun k => [.mov32 .rax (.mem (at_ .rbx (4 * k)))] ++
    (if be then [.bswap32 .rax] else []) ++ [.store32 (at_ .rbp (4 * k)) .rax]

/-- The `n` 64-bit words at `rbx`, written to `rbp` big-endian. -/
def out64 (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.mov .rax (.mem (at_ .rbx (8 * k))), .bswap .rax, .store (at_ .rbp (8 * k)) .rax]

end VG.Impl.MdStream.X86_64
