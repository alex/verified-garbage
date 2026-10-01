import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Impl.Sha512.Arm

/-!
# BLAKE2b compression function: ARMv7 implementation

`vg_blake2b_compress(state = r0, blocks = r1, n = r2, t, last, scratch)`: AAPCS
passes the 64-bit `t` in an even register pair, and `r3` is the only one
left, so `t` (stack arguments 0 and 1, low word first), `last` (2) and
`scratch` (3) are on the stack.

* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory: little-endian), as in SHA-512 (`Impl/Sha512/Arm.lean`, whose
  macros for loads, stores, additions and constants this uses): `adds` of the
  low halves and `adc` of the high halves add, and a rotation is two shifted
  halves of each half (`lsr` of one `eor` `lsl` of the other), except the
  rotation by 32, which swaps the halves and needs no instruction: the code
  takes the halves from the other registers.
* The work vector `v[0..15]` lives in `scratch[0, 128)` (word `k` at `8k`).
  Each `G` loads its four words into `r4`–`r11`, its two message words in
  turn into `r12`/`lr` and `r6`/`lr` straight from the block, and stores the
  four words back; the rotations rename the registers, so the code takes
  each result from where it ends up. The twelve rounds are fully unrolled.
* `r0` (`state`) is never written, `r1` is the current block, `r2` the
  count of blocks left, and `r3` the scratch space. `r4`–`r11` and `lr` are
  saved in `scratch[128, 164)` and restored at the end.
* The offset counter is kept in `scratch`: its low 64 bits at `[168, 176)`
  and the bits above (the carries out of them: at most one, as `t` is below
  2⁶⁴ and there are fewer than 2³² blocks) at `[176, 184)`, the high word of
  which stays zero. `[184, 192)` holds the flag word (all ones if
  `last ≠ 0`, computed without a branch) and `[192, 200)` zero: the IV words
  `8 + k` are XORed with the 64-bit word at `tweak k`, so that words 12, 13
  and 14 take the counter and the flag and the others zero.
* The only branches are on `n`, and every address is `state`, `scratch`,
  `blocks` (advanced by 128) or `sp` plus a constant, so only the pointers
  and `n` can affect timing.
-/

namespace VG.Impl.Blake2.Arm.B

open VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64 const64)

/-- `++`, grouping to the right (see `Impl/Sha512/Arm.lean`). -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `(dl, dh) := (dl, dh) ⊕ (l, h)` -/
def xor64 (dl dh l h : Reg) : List Instr := [.dp .eor dl dl (.reg l), .dp .eor dh dh (.reg h)]

/-- `(t, h) := (l, h) >>> n` for `0 < n < 32`: the result's low half in `t`,
its high half in `h` (`l` is then free). -/
def rotr (n : Nat) (t l h : Reg) : List Instr :=
  [.mov t (.shifted l .lsr n), .dp .eor t t (.shifted h .lsl (32 - n)),
   .mov h (.shifted h .lsr n), .dp .eor h h (.shifted l .lsl (32 - n))]

/-- `(t, h) := (l, h) >>> n` for `32 < n < 64`. -/
def rotr' (n : Nat) (t l h : Reg) : List Instr :=
  [.mov t (.shifted h .lsr (n - 32)), .dp .eor t t (.shifted l .lsl (64 - n)),
   .mov h (.shifted h .lsl (64 - n)), .dp .eor h h (.shifted l .lsr (n - 32))]

/-- `G` (RFC 7693 §3.1) on the words at `[r3, #a]`, …, `[r3, #d]`, with the
message words at `[r1, #x]` and `[r1, #y]`, for BLAKE2b's rotations
`(32, 24, 16, 63)`. -/
def g (a b c d x y : Nat) : List Instr :=
  ld .r4 .r5 .r3 a +++ ld .r6 .r7 .r3 b +++ ld .r8 .r9 .r3 c +++ ld .r10 .r11 .r3 d +++
  -- a := a + b + m[x]
  add64 .r4 .r5 .r6 .r7 +++ ld .r12 .lr .r1 x +++ add64 .r4 .r5 .r12 .lr +++
  -- d := (d ⊕ a) >>> 32: in (r11, r10)
  xor64 .r10 .r11 .r4 .r5 +++
  -- c := c + d
  add64 .r8 .r9 .r11 .r10 +++
  -- b := (b ⊕ c) >>> 24: in (r12, r7)
  xor64 .r6 .r7 .r8 .r9 +++ rotr 24 .r12 .r6 .r7 +++
  -- a := a + b + m[y]
  ld .r6 .lr .r1 y +++ add64 .r4 .r5 .r12 .r7 +++ add64 .r4 .r5 .r6 .lr +++
  -- d := (d ⊕ a) >>> 16: in (r6, r10)
  xor64 .r11 .r10 .r4 .r5 +++ rotr 16 .r6 .r11 .r10 +++
  -- c := c + d
  add64 .r8 .r9 .r6 .r10 +++
  -- b := (b ⊕ c) >>> 63: in (r11, r7)
  xor64 .r12 .r7 .r8 .r9 +++ rotr' 63 .r11 .r12 .r7 +++
  st .r4 .r5 .r3 a +++ st .r11 .r7 .r3 b +++ st .r8 .r9 .r3 c +++ st .r6 .r10 .r3 d

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g (8 * x) (8 * y) (8 * z) (8 * u) (8 * (Spec.Blake2.sigmaAt r (2 * i)).val)
    (8 * (Spec.Blake2.sigmaAt r (2 * i + 1)).val))

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (gAt r 0 0 4 8 12) <| .seq (gAt r 1 1 5 9 13) <| .seq (gAt r 2 2 6 10 14) <|
  .seq (gAt r 3 3 7 11 15) <| .seq (gAt r 4 0 5 10 15) <| .seq (gAt r 5 1 6 11 12) <|
  .seq (gAt r 6 2 7 8 13) (gAt r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## The layout of `scratch` -/

/-- The low 64 bits of the counter, the bits above, the flag word, zero. -/
def ctrLo : Nat := 168
def ctrHi : Nat := 176
def flagOff : Nat := 184
def zeroOff : Nat := 192

/-- The word XORed into IV word `k` (word `8 + k` of the work vector). -/
def tweak (k : Nat) : Nat :=
  if k = 4 then ctrLo else if k = 5 then ctrHi else if k = 6 then flagOff else zeroOff

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 128), (.r5, 132), (.r6, 136), (.r7, 140), (.r8, 144), (.r9, 148), (.r10, 152),
   (.r11, 156), (.lr, 160)]

/-! ## One block -/

/-- Word `k` of the state into word `k` of the work vector. -/
def ldH (k : Nat) : List Instr := ld .r4 .r5 .r0 (8 * k) ++ st .r4 .r5 .r3 (8 * k)

/-- Word `8 + k` of the work vector: IV word `k` XOR its tweak. -/
def ldIV (k : Nat) : List Instr :=
  const64 .r4 .r5 (Spec.Blake2.b.IV.toList.getD k 0) +++ ld .r6 .r7 .r3 (tweak k) +++
  xor64 .r4 .r5 .r6 .r7 +++ st .r4 .r5 .r3 (64 + 8 * k)

/-- `h[k] := h[k] ⊕ v[k] ⊕ v[k + 8]`. -/
def finH (k : Nat) : List Instr :=
  ld .r4 .r5 .r0 (8 * k) +++ ld .r6 .r7 .r3 (8 * k) +++ ld .r8 .r9 .r3 (64 + 8 * k) +++
  xor64 .r4 .r5 .r6 .r7 +++ xor64 .r4 .r5 .r8 .r9 +++ st .r4 .r5 .r0 (8 * k)

/-- Initialize the work vector (RFC 7693 §3.2). -/
def init : List Instr := (List.range 8).flatMap ldH ++ (List.range 8).flatMap ldIV

/-- XOR the two halves of the work vector into the state. -/
def fin : List Instr := (List.range 8).flatMap finH

/-- Advance the counter by 128 (with the carries out of its low 64 bits into
the high word), the block pointer to the next block, and decrement the count
of blocks (setting Z when it reaches 0). `adc` sets no flags, so the carry
out of the low word is first made a register (`r7`). -/
def advance : List Instr :=
  [.ldr .r4 .r3 ctrLo, .ldr .r5 .r3 (ctrLo + 4), .ldr .r6 .r3 ctrHi,
   .adds .r4 .r4 (.imm 128), .mov .r7 (.imm 0), .adc .r7 .r7 (.imm 0),
   .adds .r5 .r5 (.reg .r7), .adc .r6 .r6 (.imm 0),
   .str .r4 .r3 ctrLo, .str .r5 .r3 (ctrLo + 4), .str .r6 .r3 ctrHi,
   .dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.imm 1)]

def body : Prog isa := .seq (.block init) (.seq (rounds 12) (.block (fin ++ advance)))

/-! ## The whole function -/

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load `scratch`, store the counter (its high bits start at 0), save the
registers, and store the flag word `0 - ((0 - last) | last) >> 31` and zero.
The stack arguments are read before the registers are saved, through `r12`. -/
def setup : List Instr :=
  [.ldrSp .r3 12, .ldrSp .r12 0, .str .r12 .r3 ctrLo, .ldrSp .r12 4, .str .r12 .r3 (ctrLo + 4),
   .ldrSp .r12 8] ++ save ++
  [.mov .r6 (.imm 0), .str .r6 .r3 ctrHi, .str .r6 .r3 (ctrHi + 4), .str .r6 .r3 zeroOff,
   .str .r6 .r3 (zeroOff + 4),
   .dp .sub .r8 .r6 (.reg .r12), .dp .orr .r8 .r8 (.reg .r12),
   .mov .r8 (.shifted .r8 .lsr 31), .dp .sub .r8 .r6 (.reg .r8),
   .str .r8 .r3 flagOff, .str .r8 .r3 (flagOff + 4), .cmp .r2 (.imm 0)]

def compress : Prog isa :=
  .seq (.block setup) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Blake2.Arm.B
