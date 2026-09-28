import VerifiedGarbage.Impl.Sha256.Arm

/-!
# Streaming SHA-256: 32-bit ARM implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`). The same algorithm as on AArch64
(`VG.Impl.Sha256.AArch64.Stream`):

* `init(state = r0)` stores `H⁽⁰⁾`.
* `update(state = r0, count = r2:r3, data = [sp], len = [sp, #4],
  scratch = [sp, #8])` processes one block per iteration: straight from
  `data` while the buffer is empty and a whole block remains, otherwise by
  copying bytes into the buffer, compressing it once it is full.
* `finalize(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])` pads
  the buffered bytes (one or two blocks), compresses them and writes the
  digest.

Blocks are compressed by calling `vg_sha256_compress`, with
`scratch[0..112)` as its scratch space. Its code never writes `r0` or `r3`,
so `state` stays in `r0` and `scratch` in `r3`; it preserves `r4`–`r11`, so
our other variables live in `r4`–`r8`. Our caller's `r4`–`r11` are saved in
`scratch[112..144)`, and our return address (`lr`, which the calls
overwrite) in `scratch[144..148)`.

Byte `r` of the buffer is addressed as `[r1, #32]` with `r1 = state + r`
computed just before the access, and `data` is consumed through a pointer
that advances. Every comparison is a `cmp` or `subs` tested with `eq`/`ne`.
Every address and branch depends only on `sp`, the pointers, `count` and
`len`.
-/

namespace VG.Impl.Sha256.Arm.Stream

open VG.Arm
open VG.Impl.Sha256.Arm (compress)

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movw .r12 (Spec.Sha256.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Sha256.H0[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 112), (.r5, 116), (.r6, 120), (.r7, 124), (.r8, 128), (.r9, 132), (.r10, 136), (.r11, 140),
    (.lr, 144)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str r b d

/-- Restore them from `scratch` in `r3`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- A call of `vg_sha256_compress`. -/
def compressCall : Prog isa := .call "vg_sha256_compress" compress

/-- Compress the block at `r1` into the hash value at `r0`, with scratch
space `r3`. -/
def compressAt : Prog isa := .seq (.block [.mov .r2 (.imm 1)]) compressCall

/-! ## `update`

Registers: `r4` = bytes in the buffer (`r`), `r5` = `data`, `r6` = bytes of
`data` left, `r7` = whether this iteration compresses a block (at `r1`).
The loop runs while `r6 ≠ 0`, so each iteration starts with `r6 ≥ 1` and
`r4 < 64`. -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [.mov .r1 (.reg .r5), .dp .add .r5 .r5 (.imm 64), .dp .sub .r6 .r6 (.imm 64), .mov .r7 (.imm 1)]

/-- Copy `n = min(64 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- r8 := 64 - r; if len < 64 and len + r < 64 (i.e. len < 64 - r), r8 := len.
  .seq (.block [.mov .r8 (.imm 64), .dp .sub .r8 .r8 (.reg .r4), .mov .r12 (.shifted .r6 .lsr 6),
      .cmp .r12 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr 6), .cmp .r12 (.imm 0)])
        (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
      (.block []))
  (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
  (.seq (.loop (.block [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 32,
      .dp .add .r5 .r5 (.imm 1), .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]) .ne)
  -- Full: compress the buffer.
  (.seq (.block [.cmp .r4 (.imm 64)])
    (.ite .eq (.block [.dp .add .r1 .r0 (.imm 32), .mov .r4 (.imm 0), .mov .r7 (.imm 1)])
      (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.mov .r7 (.imm 0), .cmp .r4 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.mov .r12 (.shifted .r6 .lsr 6), .cmp .r12 (.imm 0)]) (.ite .eq fill (.block direct)))
      fill)
  (.seq (.seq (.block [.cmp .r7 (.imm 0)]) (.ite .eq (.block []) compressAt))
    (.block [.cmp .r6 (.imm 0)])))

def update : Prog isa :=
  .seq (.block ([.ldrSp .r12 8] ++ save .r12 ++ [.mov .r3 (.reg .r12), .dp .and .r4 .r2 (.imm 63),
      .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r6 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.loop updateBody .ne))
    (.block restore))

/-! ## `finalize`

Registers: `r4`, `r5` = `count` (low, high), `r6` = `out`, `r7` = bytes in
the buffer (`r`), `r8` = 1 while the block being padded is not the last one
(then 0). -/

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 64, or to 56 in the last block.
  .seq (.block [.mov .r9 (.imm 64), .cmp .r8 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r9 (.imm 56)]) (.block []))
  (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r7)])
  (.seq (.ite .eq (.block [])
      (.loop (.block [.dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 32, .dp .add .r7 .r7 (.imm 1),
        .subs .r9 .r9 (.imm 1)]) .ne))
  -- In the last block, the message length in bits (`8 * count`), big-endian.
  (.seq (.block [.cmp .r8 (.imm 0)])
  (.seq (.ite .eq
      (.block [.mov .r9 (.shifted .r5 .lsl 3), .dp .orr .r9 .r9 (.shifted .r4 .lsr 29), .rev .r9 .r9,
        .str .r9 .r0 88, .mov .r9 (.shifted .r4 .lsl 3), .rev .r9 .r9, .str .r9 .r0 92])
      (.block []))
  (.seq (.block [.dp .add .r1 .r0 (.imm 32)])
  (.seq compressAt
    (.block [.mov .r7 (.imm 0), .subs .r8 .r8 (.imm 1)]))))))))

def finalize : Prog isa :=
  .seq (.block ([.ldrSp .r12 4] ++ save .r12 ++ [.mov .r4 (.reg .r2), .mov .r5 (.reg .r3),
      .mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r7 .r4 (.imm 63),
      -- The `0x80` byte.
      .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 32, .dp .add .r7 .r7 (.imm 1),
      -- Two blocks iff that leaves fewer than 8 bytes for the length (r ≥ 57).
      .dp .add .r8 .r7 (.imm 7), .mov .r8 (.shifted .r8 .lsr 6)]))
  (.seq (.loop finalizeBody .eq)
    (.block ((List.range 8).flatMap (fun k =>
        [.ldr .r9 .r0 (4 * k), .rev .r9 .r9, .str .r9 .r6 (4 * k)]) ++
      restore)))

end VG.Impl.Sha256.Arm.Stream
