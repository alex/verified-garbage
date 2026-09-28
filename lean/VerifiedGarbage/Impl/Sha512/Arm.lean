import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.Arm.Isa

/-!
# SHA-512 compression function: ARMv7 implementation

The compression of one block, inlined by the streaming functions
(`VG.Impl.Sha512.Arm.Stream`); there is no stand-alone
`vg_sha512_compress` on this target. Its signature gives the compression
function 176 bytes of scratch space, which with 13 registers cannot hold the
message schedule (128 bytes), the working variables (64 bytes) and the hash
value's pointer, the blocks' pointer and count.

With `state` in `r0` and `scratch` in `r3`, it compresses the block in the
streaming state's buffer (`state[64..192)`) into the hash value
(`state[0..64)`):

* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory: little-endian), and is processed in a pair of registers: `adds` of
  the low halves and `adc` of the high halves add, and a rotation or shift of
  the word is two shifts of each half.
* The message schedule is a 16-word window kept in the buffer itself: word
  `Wₜ` (`t < 16`) replaces the block's big-endian bytes `8t … 8t + 7`
  (`rev` of each half, and the halves swapped), and `Wₜ` (`t ≥ 16`) replaces
  `Wₜ₋₁₆`. The buffer is left holding the end of the schedule.
* The working variables `a … h` are in `scratch[0..64)`; the fully unrolled
  rounds rename them: in round `t`, variable `k` is at `vOff t k`.
* It uses `r1`, `r2` and `r7`–`r12`; it reads `r0` and `r3` and does not
  change `r4`–`r6`, `lr` or anything else.
* No address and no branch depends on anything but `r0` and `r3`.
-/

namespace VG.Impl.Sha512.Arm

open VG.Arm
open VG.Spec.Sha512 (K)

/-- The low half of a 64-bit word. -/
def lo (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The high half of a 64-bit word. -/
def hi (x : BitVec 64) : BitVec 32 := x.extractLsb' 32 32

/-- Register pairs (low, high). -/
def X0 : Reg := .r1
def X1 : Reg := .r2
def Y0 : Reg := .r7
def Y1 : Reg := .r8
def Z0 : Reg := .r9
def Z1 : Reg := .r10
def E0 : Reg := .r11
def E1 : Reg := .r12

/-- The offset from `r0` of `W[j mod 16]`, in the buffer. -/
def wOff (j : Nat) : Nat := 64 + 8 * (j % 16)

/-- The offset from `r3` of working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def vOff (t k : Nat) : Nat := 8 * ((k + 8 - t % 8) % 8)

/-- Load the word at `[b, #off]` into `l` (low half) and `h`. -/
def ld (l h b : Reg) (off : Nat) : List Instr := [.ldr l b off, .ldr h b (off + 4)]

/-- Store `l` (low half) and `h` as the word at `[b, #off]`. -/
def st (l h b : Reg) (off : Nat) : List Instr := [.str l b off, .str h b (off + 4)]

/-- `(dl, dh) := (dl, dh) + (l, h)` -/
def add64 (dl dh l h : Reg) : List Instr := [.adds dl dl (.reg l), .adc dh dh (.reg h)]

/-- `(l, h) := k` -/
def const64 (l h : Reg) (k : BitVec 64) : List Instr :=
  [.movw l ((lo k).extractLsb' 0 16), .movt l ((lo k).extractLsb' 16 16),
   .movw h ((hi k).extractLsb' 0 16), .movt h ((hi k).extractLsb' 16 16)]

/-- A term of `Σ₀`, `Σ₁`, `σ₀` or `σ₁`. -/
inductive Op
  /-- `ROTRⁿ` (`0 < n < 64`, `n ≠ 32`) -/
  | rotr (n : Nat)
  /-- `SHRⁿ` (`0 < n < 32`) -/
  | shr (n : Nat)
  deriving DecidableEq, Repr

/-- The low half of a term, as two shifted halves (with no bits in common) of
the word in `(l, h)`. -/
def Op.lo (l h : Reg) : Op → List Op2
  | .rotr n => if n < 32 then [.shifted l .lsr n, .shifted h .lsl (32 - n)]
      else [.shifted h .lsr (n - 32), .shifted l .lsl (64 - n)]
  | .shr n => [.shifted l .lsr n, .shifted h .lsl (32 - n)]

/-- The high half of a term. -/
def Op.hi (l h : Reg) : Op → List Op2
  | .rotr n => if n < 32 then [.shifted h .lsr n, .shifted l .lsl (32 - n)]
      else [.shifted l .lsr (n - 32), .shifted h .lsl (64 - n)]
  | .shr n => [.shifted h .lsr n]

/-- `d := p₀ ⊕ p₁ ⊕ …` -/
def xorOf (d : Reg) : List Op2 → List Instr
  | [] => []
  | p :: ps => .mov d p :: ps.map fun p => .dp .eor d d p

/-- `(dl, dh) :=` the exclusive or of the terms `ops` of the word in `(l, h)`. -/
def sig (dl dh l h : Reg) (ops : List Op) : List Instr :=
  xorOf dl (ops.flatMap (Op.lo l h)) ++ xorOf dh (ops.flatMap (Op.hi l h))

/-- The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁`. -/
def bsig0 : List Op := [.rotr 28, .rotr 34, .rotr 39]
def bsig1 : List Op := [.rotr 14, .rotr 18, .rotr 41]
def ssig0 : List Op := [.rotr 1, .rotr 8, .shr 7]
def ssig1 : List Op := [.rotr 19, .rotr 61, .shr 6]

/-- `(Z0, X0) := Ch(e, f, g)`, with `e` in `(X0, X1)` and `f`, `g` at `[r3, #f]`,
`[r3, #g]`, as `((f ⊕ g) ∧ e) ⊕ g`. -/
def chW (f g : Nat) : List Instr :=
  [.ldr Z0 .r3 f, .ldr Z1 .r3 g, .dp .eor Z0 Z0 (.reg Z1), .dp .and Z0 Z0 (.reg X0),
   .dp .eor Z0 Z0 (.reg Z1),
   .ldr X0 .r3 (f + 4), .ldr Z1 .r3 (g + 4), .dp .eor X0 X0 (.reg Z1), .dp .and X0 X0 (.reg X1),
   .dp .eor X0 X0 (.reg Z1)]

/-- `(Z0, X0) := Maj(a, b, c)`, with `a` in `(X0, X1)` and `b`, `c` at `[r3, #b]`,
`[r3, #c]`, as `((a ∨ b) ∧ c) ∨ (a ∧ b)`. -/
def majW (b c : Nat) : List Instr :=
  [.ldr Z0 .r3 b, .dp .and Z1 X0 (.reg Z0), .dp .orr Z0 X0 (.reg Z0), .ldr X0 .r3 c,
   .dp .and Z0 Z0 (.reg X0), .dp .orr Z0 Z0 (.reg Z1),
   .ldr X0 .r3 (b + 4), .dp .and Z1 X1 (.reg X0), .dp .orr X0 X1 (.reg X0), .ldr X1 .r3 (c + 4),
   .dp .and X0 X0 (.reg X1), .dp .orr X0 X0 (.reg Z1)]

/-- `Wₜ` for `t < 16`, in place of the block's bytes at `[r0, #o]`. -/
def loadW (o : Nat) : List Instr :=
  [.ldr X0 .r0 o, .ldr X1 .r0 (o + 4), .rev X0 X0, .rev X1 X1, .str X1 .r0 o, .str X0 .r0 (o + 4)]

/-- `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆` for `t ≥ 16`, with `Wₜ₋ᵢ` at
`[r0, #oᵢ]`, in place of `Wₜ₋₁₆`. The additions are in the order of the
specification. -/
def expandW (o2 o7 o15 o16 : Nat) : List Instr :=
  ld X0 X1 .r0 o2 ++ sig Y0 Y1 X0 X1 ssig1 ++
  ld Z0 Z1 .r0 o7 ++ add64 Y0 Y1 Z0 Z1 ++
  ld X0 X1 .r0 o15 ++ sig Z0 Z1 X0 X1 ssig0 ++ add64 Y0 Y1 Z0 Z1 ++
  ld Z0 Z1 .r0 o16 ++ add64 Y0 Y1 Z0 Z1 ++
  st Y0 Y1 .r0 o16

/-- Store `Wₜ` in its slot. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then loadW (wOff t) else expandW (wOff (t + 14)) (wOff (t + 9)) (wOff (t + 1)) (wOff t)

/-- A round with the working variables at `[r3, #a]`, …, `[r3, #h]`, the
constant `k` and the message word at `[r0, #w]`. The additions are in the
order of the specification: `T₁` is accumulated in `(Y0, Y1)`, `d + T₁` in
`(E0, E1)`, and then `T₁ + T₂` in `(Y0, Y1)`. -/
def roundW (a b c d e f g h : Nat) (k : BitVec 64) (w : Nat) : List Instr :=
  -- T₁ := h + Σ₁(e) + Ch(e, f, g) + Kₜ + Wₜ
  ld Y0 Y1 .r3 h ++ ld X0 X1 .r3 e ++ sig Z0 Z1 X0 X1 bsig1 ++ add64 Y0 Y1 Z0 Z1 ++
  chW f g ++ add64 Y0 Y1 Z0 X0 ++
  const64 Z0 Z1 k ++ add64 Y0 Y1 Z0 Z1 ++
  ld Z0 Z1 .r0 w ++ add64 Y0 Y1 Z0 Z1 ++
  -- e' := d + T₁
  ld E0 E1 .r3 d ++ add64 E0 E1 Y0 Y1 ++
  -- a' := (T₁ + Σ₀(a)) + Maj(a, b, c)
  ld X0 X1 .r3 a ++ sig Z0 Z1 X0 X1 bsig0 ++ add64 Y0 Y1 Z0 Z1 ++
  majW b c ++ add64 Y0 Y1 Z0 X0 ++
  st Y0 Y1 .r3 h ++ st E0 E1 .r3 d

/-- Round `t`. -/
def round (t : Nat) : List Instr :=
  roundW (vOff t 0) (vOff t 1) (vOff t 2) (vOff t 3) (vOff t 4) (vOff t 5) (vOff t 6) (vOff t 7)
    (K t) (wOff t)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Copy word `k` of the hash value to the working variables (`vOff 0 k = 8k`). -/
def loadH (k : Nat) : List Instr := ld X0 X1 .r0 (8 * k) ++ st X0 X1 .r3 (8 * k)

/-- Add word `k` of the working variables (`80 % 8 = 0`, so at `vOff 80 k = 8k`)
into the hash value, as `a + H₀` etc. -/
def addH (k : Nat) : List Instr :=
  ld Z0 Z1 .r3 (8 * k) ++ ld X0 X1 .r0 (8 * k) ++ add64 Z0 Z1 X0 X1 ++ st Z0 Z1 .r0 (8 * k)

def load : List Instr := (List.range 8).flatMap loadH

def update : List Instr := (List.range 8).flatMap addH

/-- Compress the block in the buffer into the hash value. -/
def compress : Prog isa := .seq (.block load) (.seq (rounds 80) (.block update))

end VG.Impl.Sha512.Arm
