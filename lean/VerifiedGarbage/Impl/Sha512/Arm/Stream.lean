import VerifiedGarbage.Impl.Sha512.Arm

/-!
# Streaming SHA-512: 32-bit ARM implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`); each 64-bit word of the hash
value is stored little-endian, so as its low half followed by its high half.

* `init iv (state = r0)` stores the initial hash value `iv`.
* `update(state = r0, count = r2:r3, data = [sp], len = [sp, #4],
  scratch = [sp, #8])` processes the data in pieces: each iteration copies
  as many bytes as fit into the buffer (a whole block when the buffer is
  empty and a whole block remains), and compresses the buffer once it is
  full.
* `finalize(state = r0, count = r2:r3, out = [sp], scratch = [sp, #4])` pads
  the buffered bytes (one or two blocks), compresses them and writes the
  final hash value.

The buffer is compressed by calling `vg_sha512_compress`, with
`scratch[0..224)` as its scratch space. Its code never writes `r0` or `r3`,
so `state` stays in `r0` and `scratch` in `r3`; it preserves `r4`–`r11`, so
our variables live in `r4`–`r6`. Our caller's `r4`–`r11` and our return
address (`lr`, which the calls overwrite) are saved in `scratch[224..260)`.
`finalize` also keeps `count` in `scratch[260..268)`.

Byte `r` of the buffer is addressed as `[r1, #64]` with `r1 = state + r`
computed just before the access, and `data` is consumed through a pointer
that advances. Every comparison is a `cmp` or `subs` tested with `eq`/`ne`.
Every address and branch depends only on `sp`, the pointers, `count` and
`len`.
-/

namespace VG.Impl.Sha512.Arm.Stream

open VG.Arm
open VG.Impl.Sha512.Arm (compress lo hi)

/-- Store word `k` of `iv`. -/
def initW (iv : Spec.Sha512.HashValue) (k : Nat) : List Instr :=
  [.movw .r12 ((lo iv[k]!).extractLsb' 0 16), .movt .r12 ((lo iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k),
   .movw .r12 ((hi iv[k]!).extractLsb' 0 16), .movt .r12 ((hi iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k + 4)]

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap (initW iv))

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 224), (.r5, 228), (.r6, 232), (.r7, 236), (.r8, 240), (.r9, 244), (.r10, 248), (.r11, 252),
    (.lr, 256)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str r b d

/-- Restore them from `scratch` in `r3`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- A call of `vg_sha512_compress`. -/
def compressCall : Prog isa := .call "vg_sha512_compress" compress

/-- Compress the buffer of the state at `r0` into its hash value, with
scratch space `r3`. -/
def compressAt : Prog isa := .seq (.block [.dp .add .r1 .r0 (.imm 64), .mov .r2 (.imm 1)]) compressCall

/-! ## `update`

Registers: `r4` = bytes in the buffer (`r`), `r5` = `data`, `r6` = bytes of
`data` left. The loop runs while `r6 ≠ 0`, so each iteration starts with
`r6 ≥ 1` and `r4 < 128`. -/

/-- Copy `n = min(128 - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- r8 := 128 - r; if len < 128 and len + r < 128 (i.e. len < 128 - r), r8 := len.
  .seq (.block [.mov .r8 (.imm 128), .dp .sub .r8 .r8 (.reg .r4), .mov .r12 (.shifted .r6 .lsr 7),
      .cmp .r12 (.imm 0)])
  (.seq (.ite .eq
      (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr 7), .cmp .r12 (.imm 0)])
        (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
      (.block []))
  (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
  (.seq (.loop (.block [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64,
      .dp .add .r5 .r5 (.imm 1), .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]) .ne)
  -- Full: compress the buffer.
  (.seq (.block [.cmp .r4 (.imm 128)])
    (.ite .eq (.seq compressAt (.block [.mov .r4 (.imm 0)])) (.block []))))))

def updateBody : Prog isa := .seq fill (.block [.cmp .r6 (.imm 0)])

def update : Prog isa :=
  .seq (.block ([.ldrSp .r12 8] ++ save .r12 ++ [.mov .r3 (.reg .r12), .dp .and .r4 .r2 (.imm 127),
      .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r6 (.imm 0)]))
  (.seq (.ite .eq (.block []) (.loop updateBody .ne))
    (.block restore))

/-! ## `finalize`

Registers: `r4` = bytes in the buffer (`r`), `r5` = 1 while the block being
padded is not the last one (then 0), `r6` = `out`. -/

/-- The message length in bits as a 128-bit big-endian integer, at the end of
the buffer: `count >> 61`, then `count << 3` (modulo 2⁶⁴), from `count` in
`scratch[260..268)`. -/
def lenW : List Instr :=
  [.ldr .r9 .r3 260, .ldr .r10 .r3 264,
   .mov .r11 (.imm 0), .str .r11 .r0 176,
   .mov .r11 (.shifted .r10 .lsr 29), .rev .r11 .r11, .str .r11 .r0 180,
   .mov .r11 (.shifted .r10 .lsl 3), .dp .orr .r11 .r11 (.shifted .r9 .lsr 29), .rev .r11 .r11,
   .str .r11 .r0 184,
   .mov .r11 (.shifted .r9 .lsl 3), .rev .r11 .r11, .str .r11 .r0 188]

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 128, or to 112 in the last block.
  .seq (.block [.mov .r9 (.imm 128), .cmp .r5 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r9 (.imm 112)]) (.block []))
  (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r4)])
  (.seq (.ite .eq (.block [])
      (.loop (.block [.dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64, .dp .add .r4 .r4 (.imm 1),
        .subs .r9 .r9 (.imm 1)]) .ne))
  -- In the last block, the message length.
  (.seq (.block [.cmp .r5 (.imm 0)])
  (.seq (.ite .eq (.block lenW) (.block []))
  (.seq compressAt
    (.block [.mov .r4 (.imm 0), .subs .r5 .r5 (.imm 1)])))))))

/-- Word `k` of the final hash value, big-endian. -/
def outW (k : Nat) : List Instr :=
  [.ldr .r9 .r0 (8 * k), .ldr .r10 .r0 (8 * k + 4), .rev .r10 .r10, .rev .r9 .r9,
   .str .r10 .r6 (8 * k), .str .r9 .r6 (8 * k + 4)]

def finalize : Prog isa :=
  .seq (.block ([.ldrSp .r12 4] ++ save .r12 ++ [.str .r2 .r12 260, .str .r3 .r12 264,
      .mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r4 .r2 (.imm 127),
      -- The `0x80` byte.
      .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64, .dp .add .r4 .r4 (.imm 1),
      -- Two blocks iff that leaves fewer than 16 bytes for the length (r ≥ 113).
      .dp .add .r5 .r4 (.imm 15), .mov .r5 (.shifted .r5 .lsr 7)]))
  (.seq (.loop finalizeBody .eq)
    (.block ((List.range 8).flatMap outW ++ restore)))

end VG.Impl.Sha512.Arm.Stream
