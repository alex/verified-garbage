import VerifiedGarbage.Impl.Blake2.X86_64

/-!
# Streaming BLAKE2: x86-64 implementation

`init`, `update` and `finalize` for words of `w` bits (`Spec.Blake2.b` or
`Spec.Blake2.s`), on the streaming state of `Spec.Blake2.Repr`: the hash
value (`N = 8 · w/8` bytes) followed by a `B`-byte buffer (`B = 16 · w/8`)
holding the last block of the data so far, 1 to `B` bytes of it (none for
empty data). The caller keeps the byte count, `count`, from which the number
of buffered bytes follows.

* `init(state = rdi, outlen = rsi, key = rdx, keylen = rcx)` stores the
  initial hash value and, for a key, the key block in the buffer.
* `update(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`
  fills the buffer; if more data follows, compresses it, compresses every
  block of `data` but the last straight from `data`, and copies that last
  one (1 to `B` bytes) to the buffer.
* `finalize(state = rdi, count = rsi, out = rdx, scratch = rcx)` pads the
  buffered block with zeros, compresses it as the last block, and writes the
  hash value to `out`.

The compression function (`compress`, `Impl/Blake2/X86_64.lean`) is called
with `scratch` as its scratch space; it preserves `rbx, rbp, r12–r15`, so our
own variables live there across it (`rbx` = `state`, `r15` = `scratch`), and
our caller's values of those registers are saved in `scratch[512..560)`. It
never writes `rdi` or `r9`, which hold `state` and `scratch` when it is
called: `rbx` and `r15` are copied back from them only for the constant-time
analysis, which tracks which registers hold the base address of a region
through registers but not through memory. Every address and branch depends
only on the pointers, `count` and the lengths.
-/

namespace VG.Impl.Blake2.X86_64.Stream

open VG.X86_64
open VG.Impl.Blake2.X86_64 (at_ ws imm compress)

section
variable (w : Nat)

/-- The size of the hash value, where the buffer starts. -/
def N : Nat := 8 * ws w
/-- The block size. -/
def B : Nat := 16 * ws w

end

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 512), (.rbp, 520), (.r12, 528), (.r13, 536), (.r14, 544), (.r15, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them (`r15`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-- `[rbx + r13 + N]`: byte `r13` of the buffer. -/
def bufByte : MemOp := { base := .rbx, index := some .r13, scale := 1, disp := N w }

/-- `r13` := the number of bytes in the buffer for the byte count in `r14`:
`((count - 1) mod B) + 1`, or 0 if `count = 0`. -/
def bufLen : Prog isa :=
  .seq (.block [.mov .r13 (.reg .r14), .alu .sub .r13 (.imm 1),
      .alu .and .r13 (.imm (BitVec.ofNat 32 (B w - 1))), .alu .add .r13 (.imm 1),
      .alu .test .r14 (.reg .r14)])
    (.ite .e (.block [.mov32 .r13 (.imm 0)]) (.block []))

/-- Compress into the hash value at `rbx`, with scratch space `r15`, after
`args` set the blocks (`rsi`), their number (`rdx`), the counter (`rcx`) and
the final block flag (`r8`). -/
def compressWith (args : List Instr) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbx)] ++ args ++ [.mov .r9 (.reg .r15)]))
    (.seq (.call (if w = 64 then "vg_blake2b_compress" else "vg_blake2s_compress") (compress P))
      (.block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .r9)]))

/-- The loop copying `rax ≥ 1` bytes of `data` (at `rbp`) to the buffer, from
byte `r13` on. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .r9 { base := .rbp }, .store8 (bufByte (w := w)) .r9,
    .alu .add .rbp (.imm 1), .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne

/-! ## `update`

Registers: `rbp` = `data`, `r12` = bytes of `data` left, `r13` = bytes in the
buffer, `r14` = the byte count so far. -/

/-- Copy `min(B - r13, r12)` bytes of `data` to the buffer. -/
def fill : Prog isa :=
  .seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (B w))), .alu .sub .rax (.reg .r13),
      .alu .cmp .r12 (.reg .rax)])
  (.seq (.ite .b (.block [.mov .rax (.reg .r12)]) (.block []))
  (.seq (.block [.alu .sub .r12 (.reg .rax), .alu .add .r14 (.reg .rax), .alu .test .rax (.reg .rax)])
    (.ite .e (.block []) (copyLoop (w := w)))))

/-- Compress the (full) buffer, which is not the last block: its counter is
the byte count. -/
def compressBuf : Prog isa :=
  .seq (compressWith P [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (N w))),
      .mov32 .rdx (.imm 1), .mov .rcx (.reg .r14), .mov32 .r8 (.imm 0)])
    (.block [.mov32 .r13 (.imm 0)])

/-- If the buffer is not empty: fill it, and if more data follows, compress
it. -/
def head : Prog isa :=
  .seq (.block [.alu .test .r13 (.reg .r13)])
    (.ite .e (.block [])
      (.seq (fill (w := w)) (.seq (.block [.alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (compressBuf P)))))

/-- With the buffer empty and `r12 ≥ 1` bytes left: compress all the blocks of
`data` but the last, `(r12 - 1) / B` of them, straight from `data`, leaving
`((r12 - 1) mod B) + 1` bytes. -/
def direct : Prog isa :=
  .seq (.block [.mov .rax (.reg .r12), .alu .sub .rax (.imm 1), .shift .shr .rax (Nat.log2 (B w)),
      .alu .test .rax (.reg .rax)])
    (.ite .e (.block [])
      (.seq (compressWith P [.mov .rsi (.reg .rbp), .mov .rdx (.reg .rax), .mov .rcx (.reg .r14),
          .alu .add .rcx (.imm (BitVec.ofNat 32 (B w))), .mov32 .r8 (.imm 0)])
        (.block [.mov .rax (.reg .r12), .alu .sub .rax (.imm 1),
          .alu .and .rax (.imm (BitVec.ofNat 32 (B w - 1))), .alu .add .rax (.imm 1),
          .alu .sub .r12 (.reg .rax), .alu .add .rbp (.reg .r12), .alu .add .r14 (.reg .r12),
          .mov .r12 (.reg .rax)])))

/-- Copy the last `r12` (1 to `B`) bytes of `data` to the (empty) buffer. -/
def tail : Prog isa :=
  .seq (.block [.mov .rax (.reg .r12), .alu .add .r14 (.reg .rax), .mov32 .r12 (.imm 0)])
    (copyLoop (w := w))

/-- The rest of `data`, if any, after `head`. -/
def rest : Prog isa :=
  .seq (.block [.alu .test .r12 (.reg .r12)]) (.ite .e (.block []) (.seq (direct P) (tail (w := w))))

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save .r8 ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .r8), .mov .rbp (.reg .rdx),
    .mov .r12 (.reg .rcx), .mov .r14 (.reg .rsi)]

def update : Prog isa :=
  .seq (.block updateStart) (.seq (bufLen (w := w))
    (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .e (.block []) (.seq (head P) (rest P))) (.block restore))))

/-! ## `finalize`

Registers: `rbp` = `out`, `r13` = bytes in the buffer, `r14` = `count`. -/

/-- The loop zeroing the buffer from byte `r13` on, `rax ≥ 1` bytes (`r9 = 0`). -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (bufByte (w := w)) .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) .ne

/-- Zero the rest of the buffer. -/
def pad : Prog isa :=
  .seq (.block [.mov32 .r9 (.imm 0), .mov32 .rax (.imm (BitVec.ofNat 32 (B w))),
      .alu .sub .rax (.reg .r13)])
    (.ite .e (.block []) (zeroLoop (w := w)))

/-- Compress the buffer as the last block: its counter is the byte count. -/
def compressLast : Prog isa :=
  compressWith P [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (N w))),
    .mov32 .rdx (.imm 1), .mov .rcx (.reg .r14), .mov32 .r8 (.imm 1)]

/-- Copy the hash value (at `rbx`) to `out` (at `rbp`). -/
def output : List Instr :=
  (List.range (N w / 8)).flatMap fun k =>
    [.mov .rax (.mem (at_ .rbx (8 * k))), .store (at_ .rbp (8 * k)) .rax]

def finalize : Prog isa :=
  .seq (.block (save .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rsi)]))
    (.seq (bufLen (w := w)) (.seq (pad (w := w)) (.seq (compressLast P)
      (.block (output (w := w) ++ restore)))))

/-! ## `init`

Uses only `rax`, `rcx`, `rdx`, `rsi`, `rdi` and `r8`. -/

/-- `h := IV`, with the parameter block `0x0101kknn` XORed into `h[0]`
(`kk` = `keylen` in `rcx`, `nn` = `outlen` in `rsi`; `kk << 8` is a rotation,
as `kk < 2^(w - 8)`). -/
def initState : List Instr :=
  (List.finRange 7).flatMap (fun i =>
    [imm w .rax (P.IV[i.1 + 1]'(by omega)),
      VG.Impl.Blake2.X86_64.st w (at_ .rdi (ws w * (i.1 + 1))) .rax]) ++
  [imm w .rax (P.IV[0] ^^^ 0x01010000), .mov .r8 (.reg .rcx),
    VG.Impl.Blake2.X86_64.ror w .r8 (w - 8), VG.Impl.Blake2.X86_64.xor w .rax (.reg .r8),
    VG.Impl.Blake2.X86_64.xor w .rax (.reg .rsi), VG.Impl.Blake2.X86_64.st w (at_ .rdi 0) .rax]

/-- Zero the buffer and copy the `rcx ≥ 1` bytes of the key (at `rdx`) to it. -/
def keyBlock : Prog isa :=
  .seq (.block (.mov32 .rax (.imm 0) :: (List.range (B w / 8)).map fun j =>
      .store (at_ .rdi (N w + 8 * j)) .rax))
    (.seq (.block [.mov32 .r8 (.imm 0)])
      (.loop (.block [.movzx8 .rax { base := .rdx, index := some .r8, scale := 1 },
        .store8 { base := .rdi, index := some .r8, scale := 1, disp := N w } .rax,
        .alu .add .r8 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne))

def init : Prog isa :=
  .seq (.block (initState P ++ [.alu .test .rcx (.reg .rcx)]))
    (.ite .e (.block []) (keyBlock (w := w)))

end

end VG.Impl.Blake2.X86_64.Stream
