import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub

/-!
# ML-DSA on 32-bit ARM: rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint` each run
one loop over the 256 coefficients (`mapLoop`), with a register counting
down from 256 (`subs`), and each polynomial's pointer advanced by 4 bytes
per iteration. Those that need more than `r0`–`r3` and `r12` save `r4`–`r6`
as they need them, in frames on the stack (`saving`). There is no branch on
data: a conditional step is a mask `u >> 31` (the sign of a difference),
shifted or multiplied, or the carry of a comparison (`adc`); and
`Decompose` divides by `2γ₂` with a multiplication and shifts, as the
reference implementation does (`hbRaw`):
`f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` = `(1025, 22)` if
`γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`, which is
`⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q`; then `r₁ = f mod m` for
`m = (q - 1)/(2γ₂)` (16 or 44) is one conditional subtraction of `m`
(`csubM`), as `f ≤ m` (`hb`). `γ₂` is a public argument: the functions that
take it compare it with `(q - 1)/88` once, and run one loop for each value.

* `power2Round(t = r0, t1 = r1, t0 = r2)`, saving `r4`, `r3` counting:
  `x = a + 4095`, `t1 = x >> 13` and `t0 = (x mod 2¹³) - 4095`, plus `q` if
  negative (`fixupS`).
* `highBits(r = r0, gamma2 = r1, out = r2)`, `r1` counting: `r₁`.
* `lowBits(r = r0, gamma2 = r1, out = r2)`, `r1` counting: `a - r₁ · 2γ₂`,
  plus `q` if negative.
* `normLt(f = r0, bound = r1)`, saving `r4`, `r2` counting: `r4` becomes 1
  once a coefficient `a` has `bound ≤ a` and `bound ≤ q - a` (the carries
  of two comparisons, as `adc` turns them into numbers); the result is
  `1 - r4`.
* `makeHint(z = r0, r = r1, gamma2 = r2, h = r3)`, saving `r4`–`r6`, `r2`
  counting: `r₁` of `r` (in `r5`) and of `r + z mod q`, exclusive-ored, is
  nonzero (`(x + 63) >> 6`, as `x < 64`) exactly when the hint is 1; `r4`
  counts the 1s, and is the result.
* `useHint(h = r0, r = r1, gamma2 = r2, out = r3)`, saving `r4`–`r6`, `r2`
  counting: `(f + m + δ) mod m` by two conditional subtractions of `m`, for
  `δ` 0 if the hint word is 0 and else 1 if `f · 2γ₂ < a` (`r₀ > 0`, the
  carry of `f · 2γ₂ - a` clear), -1 otherwise: `δ = (1 - 2c) · h'` for the
  carry `c` and `h' = ((0 - h) | h) >> 31`.
-/

namespace VG.Impl.MlDsa.Arm.Round

open VG.Arm
open VG.Impl.MlDsa.Arm.Arith (saving subQ fixupS)

/-- The loop over the coefficients, counted by `cnt`; `body` ends with
`subs cnt, cnt, #1`. -/
def mapLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .seq (.block [.mov cnt (.imm 256)]) (.loop (.block body) .ne)

/-! ## `Decompose` -/

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-- The multiplier `M`. -/
def dMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def dShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `2^(S-1)`. -/
def dAdd (g : Nat) : Nat := if g = 261888 then 2 ^ 21 else 2 ^ 23

/-- `m = (q - 1)/(2γ₂)`. -/
def dMod (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- `r ← r + t · m`, for `t` 0 or 1, as shifts (`16 = 2⁴`, `44 = 2⁵ + 2³ + 2²`). -/
def addMaskM (g : Nat) (r t : Reg) : List Instr :=
  if g = 261888 then [.dp .add r r (.shifted t .lsl 4)]
  else [.dp .add r r (.shifted t .lsl 5), .dp .add r r (.shifted t .lsl 3), .dp .add r r (.shifted t .lsl 2)]

/-- `r ← r - m`, plus `m` if that is negative, with `t` as the mask. -/
def csubM (g : Nat) (r t : Reg) : List Instr :=
  [.dp .sub r r (.imm (BitVec.ofNat 32 (dMod g))), .mov t (.shifted r .lsr 31)] ++ addMaskM g r t

/-- `x ← f` for `a = x`, with `t` a temporary. -/
def hbRaw (g : Nat) (x t : Reg) : List Instr :=
  [.dp .add x x (.imm 127), .mov x (.shifted x .lsr 7), .movw t (BitVec.ofNat 16 (dMul g)), .mul x x t,
   .dp .add x x (.imm (BitVec.ofNat 32 (dAdd g))), .mov x (.shifted x .lsr (dShift g))]

/-- `x ← r₁ = f mod m` for `a = x`, with `t` a temporary. -/
def hb (g : Nat) (x t : Reg) : List Instr := hbRaw g x t ++ csubM g x t

/-- `r ← 2γ₂`. -/
def load2g (g : Nat) (r : Reg) : List Instr :=
  [.movw r (BitVec.ofNat 16 (2 * g % 65536)), .movt r (BitVec.ofNat 16 (2 * g / 65536))]

/-! ## The functions -/

def p2rBody : List Instr :=
  [.ldr .r12 .r0 0, .dp .add .r12 .r12 (.imm 4096), .dp .sub .r12 .r12 (.imm 1), .mov .r4 (.shifted .r12 .lsr 13),
   .str .r4 .r1 0, .mov .r12 (.shifted .r12 .lsl 19), .mov .r12 (.shifted .r12 .lsr 19),
   .dp .sub .r12 .r12 (.imm 4096), .dp .add .r12 .r12 (.imm 1)] ++ fixupS .r12 .r4 ++
  [.str .r12 .r2 0, .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4),
   .subs .r3 .r3 (.imm 1)]

def power2Round : Prog isa := saving [.r4] (mapLoop .r3 p2rBody)

/-- `γ₂` compared with `(q - 1)/88`. -/
def gammaCmp (r : Reg) : Instr := .cmp r (.imm (BitVec.ofNat 32 g88))

/-- The end of an iteration with two pointers `r0` and `r2`, `r1` counting. -/
def tail02 : List Instr := [.dp .add .r0 .r0 (.imm 4), .dp .add .r2 .r2 (.imm 4), .subs .r1 .r1 (.imm 1)]

def hbBody (g : Nat) : List Instr := [.ldr .r3 .r0 0] ++ hb g .r3 .r12 ++ [.str .r3 .r2 0] ++ tail02

def highBits : Prog isa :=
  .seq (.block [gammaCmp .r1]) (.ite .eq (mapLoop .r1 (hbBody g88)) (mapLoop .r1 (hbBody g32)))

def lbBody (g : Nat) : List Instr :=
  [.ldr .r3 .r0 0] ++ hb g .r3 .r12 ++ load2g g .r12 ++
    [.mul .r3 .r3 .r12, .ldr .r12 .r0 0, .dp .sub .r3 .r12 (.reg .r3)] ++ fixupS .r3 .r12 ++
    [.str .r3 .r2 0] ++ tail02

def lowBits : Prog isa :=
  .seq (.block [gammaCmp .r1]) (.ite .eq (mapLoop .r1 (lbBody g88)) (mapLoop .r1 (lbBody g32)))

def nlBody : List Instr :=
  [.ldr .r3 .r0 0, .movw .r12 0xE001, .movt .r12 0x7F, .dp .sub .r12 .r12 (.reg .r3), .cmp .r3 (.reg .r1),
   .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0), .cmp .r12 (.reg .r1), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
   .dp .and .r3 .r3 (.reg .r12), .dp .orr .r4 .r4 (.reg .r3), .dp .add .r0 .r0 (.imm 4), .subs .r2 .r2 (.imm 1)]

def normLt : Prog isa :=
  saving [.r4] (.seq (.block [.mov .r4 (.imm 0)])
    (.seq (mapLoop .r2 nlBody) (.block [.mov .r0 (.imm 1), .dp .sub .r0 .r0 (.reg .r4)])))

/-- The end of an iteration with three pointers `r0`, `r1` and `r3`, `r2` counting. -/
def tail013 : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r3 .r3 (.imm 4), .subs .r2 .r2 (.imm 1)]

def mhBody (g : Nat) : List Instr :=
  [.ldr .r5 .r1 0] ++ hb g .r5 .r12 ++ [.ldr .r6 .r1 0, .ldr .r12 .r0 0, .dp .add .r6 .r6 (.reg .r12)] ++
    subQ .r6 ++ fixupS .r6 .r12 ++ hb g .r6 .r12 ++
    [.dp .eor .r6 .r6 (.reg .r5), .dp .add .r6 .r6 (.imm 63), .mov .r6 (.shifted .r6 .lsr 6), .str .r6 .r3 0,
     .dp .add .r4 .r4 (.reg .r6)] ++ tail013

def makeHint : Prog isa :=
  saving [.r4, .r5, .r6] (.seq (.block [gammaCmp .r2, .mov .r4 (.imm 0)])
    (.seq (.ite .eq (mapLoop .r2 (mhBody g88)) (mapLoop .r2 (mhBody g32))) (.block [.mov .r0 (.reg .r4)])))

def uhBody (g : Nat) : List Instr :=
  [.ldr .r12 .r1 0] ++ hbRaw g .r12 .r4 ++ load2g g .r4 ++
    [.mul .r4 .r4 .r12, .ldr .r5 .r1 0, .cmp .r4 (.reg .r5), .mov .r4 (.imm 0), .adc .r4 .r4 (.imm 0),
     .mov .r5 (.imm 1), .dp .sub .r5 .r5 (.shifted .r4 .lsl 1), .ldr .r4 .r0 0, .mov .r6 (.imm 0),
     .dp .sub .r6 .r6 (.reg .r4), .dp .orr .r6 .r6 (.reg .r4), .mov .r6 (.shifted .r6 .lsr 31), .mul .r5 .r5 .r6,
     .dp .add .r12 .r12 (.reg .r5), .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (dMod g)))] ++
    csubM g .r12 .r4 ++ csubM g .r12 .r4 ++ [.str .r12 .r3 0] ++ tail013

def useHint : Prog isa :=
  saving [.r4, .r5, .r6] (.seq (.block [gammaCmp .r2])
    (.ite .eq (mapLoop .r2 (uhBody g88)) (mapLoop .r2 (uhBody g32))))

end VG.Impl.MlDsa.Arm.Round
