import VerifiedGarbage.TCB.Arm.Isa

/-!
# Streaming Merkle–Damgård hash functions: 32-bit ARM implementation

The streaming `update` and `finalize` of MD5, SHA-1, SHA-256 and the SHA-512
family, which differ only in their sizes, in how they store the message
length and output the digest, and in the compression function they call
(`Params`).
Each hash function's `Impl/<Alg>/Arm/Stream.lean` instantiates them. The
same algorithm as on AArch64 (`VG.Impl.MdStream.AArch64`).

The streaming state (`N + B` bytes at `state`) is the hash value (`N`
bytes) followed by a `B`-byte buffer.

* `update(state = r0, count = r2:r3, data = [sp], len = [sp, #4],
  scratch = [sp, #8])` compresses, in each iteration, every whole block left
  in `data` with one call if the buffer is empty (so that implementations
  that process several blocks at once can), and otherwise copies bytes into
  the buffer, compressing it once it is full.
* `finalize(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])` pads
  the buffered bytes (one or two blocks), compresses them and writes the
  digest.

Blocks are compressed by calling the compression function (`name`, `code`),
with `scratch[0..so)` as its scratch space. Its code never writes `r0` or
`r3`, so `state` stays in `r0` and `scratch` in `r3`; it preserves
`r4`–`r11`, so our other variables live in `r4`–`r8`. Our caller's
`r4`–`r11` are saved in `scratch[so..so+32)`, and our return address (`lr`,
which the calls overwrite) in `scratch[so+32..so+36)`.

Byte `r` of the buffer is addressed as `[r1, #N]` with `r1 = state + r`
computed just before the access, and `data` is consumed through a pointer
that advances. Every comparison is a `cmp` or `subs` tested with `eq`/`ne`.
Every address and branch depends only on `sp`, the pointers, `count` and
`len`.
-/

namespace VG.Impl.MdStream.Arm

open VG.Arm

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- The block size, a power of two. -/
  B : Nat
  /-- The size of the length field at the end of the last block. -/
  L : Nat
  /-- Where our caller's registers are saved in the scratch space, after the
  compression function's own. -/
  so : Nat
  /-- Stores the length field, from `count` in `r4:r5` (low, high), at
  `r0 + N + B - L`; writes only `r9`. -/
  len : List Instr
  /-- Writes the digest, from the hash value at `r0`, to `r6`; writes only
  `r9` and `r10`. -/
  out : List Instr

variable (P : Params)

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, P.so), (.r5, P.so + 4), (.r6, P.so + 8), (.r7, P.so + 12), (.r8, P.so + 16), (.r9, P.so + 20),
    (.r10, P.so + 24), (.r11, P.so + 28), (.lr, P.so + 32)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := (saved P).map fun (r, d) => .str r b d

/-- Restore them from `scratch` in `r3`. -/
def restore : List Instr := (saved P).map fun (r, d) => .ldr r .r3 d

/-- Compress the blocks at `r1` into the hash value at `r0`, with scratch
space `r3`, after `n` sets their number in `r2`. -/
def compressWith (n : Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [n]) (.call name code)

/-- Compress one block. -/
def compressAt : String → Prog isa → Prog isa := compressWith (.mov .r2 (.imm 1))

/-- Compress `r7` blocks. -/
def compressN : String → Prog isa → Prog isa := compressWith (.mov .r2 (.reg .r7))

/-! ## `update`

Registers: `r4` = bytes in the buffer (`r`), `r5` = `data`, `r6` = bytes of
`data` left, `r7` = the number of blocks this iteration compresses (at
`r1`).
The loop runs while `r6 ≠ 0`, so each iteration starts with `r6 ≥ 1` and
`r4 < B`. -/

/-- Every whole block left, straight from `data`: `len >> log₂ B` blocks,
`(len >> log₂ B) << log₂ B` bytes. -/
def direct : List Instr :=
  [.mov .r1 (.reg .r5), .mov .r7 (.shifted .r6 .lsr (Nat.log2 P.B)),
    .mov .r12 (.shifted .r7 .lsl (Nat.log2 P.B)),
    .dp .add .r5 .r5 (.reg .r12), .dp .sub .r6 .r6 (.reg .r12)]

/-- Copy `n = min(B - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- r8 := B - r; if len < B and len + r < B (i.e. len < B - r), r8 := len.
  .seq (.block [.mov .r8 (.imm (BitVec.ofNat 32 P.B)), .dp .sub .r8 .r8 (.reg .r4),
      .mov .r12 (.shifted .r6 .lsr (Nat.log2 P.B)), .cmp .r12 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr (Nat.log2 P.B)),
          .cmp .r12 (.imm 0)])
        (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
      (.block []))
  (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
  (.seq (.loop (.block [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 P.N,
      .dp .add .r5 .r5 (.imm 1), .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]) .ne)
  -- Full: compress the buffer.
  (.seq (.block [.cmp .r4 (.imm (BitVec.ofNat 32 P.B))])
    (.ite .eq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N)), .mov .r4 (.imm 0), .mov .r7 (.imm 1)])
      (.block []))))))

def updateBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .r7 (.imm 0), .cmp .r4 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.mov .r12 (.shifted .r6 .lsr (Nat.log2 P.B)), .cmp .r12 (.imm 0)])
        (.ite .eq (fill P) (.block (direct P))))
      (fill P))
  (.seq (.seq (.block [.cmp .r7 (.imm 0)]) (.ite .eq (.block []) (compressN name code)))
    (.block [.cmp .r6 (.imm 0)])))

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block ([.ldrSp .r12 8] ++ save P .r12 ++ [.mov .r3 (.reg .r12),
      .dp .and .r4 .r2 (.imm (BitVec.ofNat 32 (P.B - 1))), .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r6 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.loop (updateBody P name code) .ne))
    (.block (restore P)))

/-! ## `finalize`

Registers: `r4`, `r5` = `count` (low, high), `r6` = `out`, `r7` = bytes in
the buffer (`r`), `r8` = 1 while the block being padded is not the last one
(then 0). -/

def finalizeBody (name : String) (code : Prog isa) : Prog isa :=
  -- Zero the buffer from `r` to `B`, or to `B - L` in the last block.
  .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 P.B)), .cmp .r8 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r9 (.imm (BitVec.ofNat 32 (P.B - P.L)))]) (.block []))
  (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r7)])
  (.seq (.ite .eq (.block [])
      (.loop (.block [.dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1),
        .subs .r9 .r9 (.imm 1)]) .ne))
  -- In the last block, the length field.
  (.seq (.block [.cmp .r8 (.imm 0)])
  (.seq (.ite .eq (.block P.len) (.block []))
  (.seq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N))])
  (.seq (compressAt name code)
    (.block [.mov .r7 (.imm 0), .subs .r8 .r8 (.imm 1)]))))))))

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block ([.ldrSp .r12 4] ++ save P .r12 ++ [.mov .r4 (.reg .r2), .mov .r5 (.reg .r3),
      .mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r7 .r4 (.imm (BitVec.ofNat 32 (P.B - 1))),
      -- The `0x80` byte.
      .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1),
      -- Two blocks iff that leaves fewer than `L` bytes for the length (r > B - L).
      .dp .add .r8 .r7 (.imm (BitVec.ofNat 32 (P.L - 1))), .mov .r8 (.shifted .r8 .lsr (Nat.log2 P.B))]))
  (.seq (.loop (finalizeBody P name code) .eq)
    (.block (P.out ++ restore P)))

/-! ## Length fields and digests -/

/-- The message length in bits (`8 * count`, from `r4:r5`), big-endian if
`be`, little-endian otherwise, at `r0 + d`. -/
def len64 (d : Nat) (be : Bool) : List Instr :=
  if be then
    [.mov .r9 (.shifted .r5 .lsl 3), .dp .orr .r9 .r9 (.shifted .r4 .lsr 29), .rev .r9 .r9, .str .r9 .r0 d,
      .mov .r9 (.shifted .r4 .lsl 3), .rev .r9 .r9, .str .r9 .r0 (d + 4)]
  else
    [.mov .r9 (.shifted .r4 .lsl 3), .str .r9 .r0 d, .mov .r9 (.shifted .r5 .lsl 3),
      .dp .orr .r9 .r9 (.shifted .r4 .lsr 29), .str .r9 .r0 (d + 4)]

/-- The `n` 32-bit words at `r0`, big-endian if `be`, little-endian
otherwise, to `r6`. -/
def out32 (n : Nat) (be : Bool) : List Instr :=
  (List.range n).flatMap fun k =>
    [.ldr .r9 .r0 (4 * k)] ++ (if be then [.rev .r9 .r9] else []) ++ [.str .r9 .r6 (4 * k)]

end VG.Impl.MdStream.Arm
