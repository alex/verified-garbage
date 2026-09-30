import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: rounding and hints

`vg_mldsa_power2round`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint` each run
one loop over the 256 coefficients (`mapLoop`), with a counter counting
down from 256 and the pointers of the polynomials advancing by 4 bytes
from coefficient 0. There is no branch on data: a conditional step uses the
sign bit of a 64-bit difference (`lsr #63`), and `Decompose` divides by
`2γ₂` with a multiplication and shifts, as the reference implementation
does (`hbRaw`): `f = ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `(M, S)` =
`(1025, 22)` if `γ₂ = (q - 1)/32` and `(11275, 24)` if `γ₂ = (q - 1)/88`,
which is `⌊(a + γ₂ - 1)/(2γ₂)⌋` for every `a < q`; then `r₁ = f mod m` for
`m = (q - 1)/(2γ₂)` (16 or 44) is `f` times the sign bit of `f - m`, as
`f ≤ m` (`hb`). `γ₂` is a public argument: the functions that take it
zero-extend it (it is a `u32`), compare it with `(q - 1)/32` and branch on
it once, to one loop for each value, which first puts `M` and `2^(S-1)` in
registers.

* `power2Round(t = x0, t1 = x1, t0 = x2)`: `x = a + 4095`, `t1 = x >> 13`
  and `t0 = x - (t1 << 13) - 4095`, plus `q` if negative.
* `highBits(r = x0, gamma2 = w1, out = x2)`: `r₁`.
* `lowBits(r = x0, gamma2 = w1, out = x2)`: `a - r₁ · 2γ₂`, plus `q` if
  negative.
* `normLt(f = x0, bound = w1)`: the top bit of `x10` stays set while every
  coefficient `a` so far has `a < bound` or `q - a < bound` (both
  differences, in 64 bits, negative for one of them); it is the result.
* `makeHint(z = x0, r = x1, gamma2 = w2, h = x3)`: `r₁` of `r` and of
  `r + z mod q`, xored, is nonzero (`(x + 63) >> 6`, as `x < 64`) exactly
  when the hint is 1; `x8` counts the 1s.
* `useHint(h = x0, r = x1, gamma2 = w2, out = x3)`: `(f + m + δ) mod m` by
  two conditional subtractions of `m`, for `δ` 0 if the hint is 0 and else 1
  if `f · 2γ₂ < a` (`r₀ > 0`), -1 otherwise (`2s - 1` for the sign bit `s`
  of `f · 2γ₂ - a`, times the hint as 0 or 1: the sign bit of `0 - h`).
-/

namespace VG.Impl.MlDsa.AArch64.Round

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub)
open VG.Impl.MlDsa.AArch64.Arith (movW qNat)

/-- The loop over the coefficients: `body`, then the pointers `ptrs` advance
and the counter `cnt` counts down from 256. -/
def mapLoop (ptrs : List Reg) (cnt : Reg) (body : List Instr) : Prog isa :=
  .seq (.block [.movz .x cnt 256 0])
    (.loop (.block (body ++ ptrs.map (fun p => .addImm .x p p 4) ++ [.subImm .x cnt cnt 1]))
      (.nonzero .x cnt))

/-- `d ← d mod m` for `d < 2m`, with `m` in `mr` and a temporary `t`. -/
def csubR (d t mr : Reg) : List Instr := [.sub .x d d mr, .lsr .x t d 63, .madd .x d t mr d]

/-! ## `Decompose` -/

/-- The values of `γ₂`: `(q - 1)/32` and `(q - 1)/88`. -/
def g32 : Nat := 261888
def g88 : Nat := 95232

/-- The multiplier `M`. -/
def dMul (g : Nat) : Nat := if g = 261888 then 1025 else 11275

/-- The shift `S`. -/
def dShift (g : Nat) : Nat := if g = 261888 then 22 else 24

/-- `2^(S-1) / 2¹⁶`, which `movz … lsl #16` shifts into place. -/
def dAddHi (g : Nat) : Nat := if g = 261888 then 32 else 128

/-- `m = (q - 1)/(2γ₂)`. -/
def dMod (g : Nat) : Nat := if g = 261888 then 16 else 44

/-- `M` in `rm` and `2^(S-1)` in `ra`. -/
def hbConsts (g : Nat) (rm ra : Reg) : List Instr :=
  [.movz .x rm (BitVec.ofNat 16 (dMul g)) 0, .movz .x ra (BitVec.ofNat 16 (dAddHi g)) 1]

/-- `f ← ⌊(⌊(a + 127)/2⁷⌋ · M + 2^(S-1)) / 2^S⌋` for `a` in `a`, with `M` in
`rm` and `2^(S-1)` in `ra`. -/
def hbRaw (g : Nat) (f a rm ra : Reg) : List Instr :=
  [.addImm .x f a 127, .lsr .x f f 7, .mul .x f f rm, .add .x f f ra, .lsr .x f f (dShift g)]

/-- `f ← r₁ = f mod m` of `a`, with a temporary `t`. -/
def hb (g : Nat) (f a t rm ra : Reg) : List Instr :=
  hbRaw g f a rm ra ++ [.subImm .x t f (dMod g), .lsr .x t t 63, .mul .x f f t]

/-- The branch on `γ₂` (in `gr`, zero-extended), through `t`: `arm g32` if
it is `(q - 1)/32`, else `arm g88`. -/
def onGamma (gr t : Reg) (arm : Nat → Prog isa) : Prog isa :=
  .seq (.block (movW t (BitVec.ofNat 32 g32) ++ [.sub .x t gr t])) (.ite (.zero .x t) (arm g32) (arm g88))

/-- `γ₂` in `gr` zero-extended first, then `main`. -/
def zext (gr : Reg) (main : Prog isa) : Prog isa := .seq (.block [.addImm .w gr gr 0]) main

/-! ## `power2Round` -/

def p2rBody : List Instr :=
  [.ldr .w .x11 .x0 0, .addImm .x .x11 .x11 4095, .lsr .x .x12 .x11 13, .str .w .x12 .x1 0,
    .lsl .x .x13 .x12 13, .sub .x .x11 .x11 .x13, .subImm .x .x11 .x11 4095, .lsr .x .x13 .x11 63,
    .madd .x .x11 .x13 .x9 .x11, .str .w .x11 .x2 0]

def power2Round : Prog isa :=
  .seq (.block (movW .x9 (BitVec.ofNat 32 qNat))) (mapLoop [.x0, .x1, .x2] .x10 p2rBody)

/-! ## `highBits` and `lowBits` -/

def hbBody (g : Nat) : List Instr := [.ldr .w .x11 .x0 0] ++ hb g .x12 .x11 .x13 .x4 .x5 ++ [.str .w .x12 .x2 0]

def highBits : Prog isa :=
  zext .x1 <| onGamma .x1 .x3 fun g => .seq (.block (hbConsts g .x4 .x5)) (mapLoop [.x0, .x2] .x6 (hbBody g))

def lbBody (g : Nat) : List Instr :=
  [.ldr .w .x11 .x0 0] ++ hb g .x12 .x11 .x13 .x4 .x5 ++
    [.mul .x .x12 .x12 .x7, .sub .x .x11 .x11 .x12, .lsr .x .x13 .x11 63, .madd .x .x11 .x13 .x9 .x11,
      .str .w .x11 .x2 0]

/-- `M`, `2^(S-1)`, `2γ₂` and `q`. -/
def lbConsts (g : Nat) : List Instr :=
  hbConsts g .x4 .x5 ++ movW .x7 (BitVec.ofNat 32 (2 * g)) ++ movW .x9 (BitVec.ofNat 32 qNat)

def lowBits : Prog isa :=
  zext .x1 <| onGamma .x1 .x3 fun g => .seq (.block (lbConsts g)) (mapLoop [.x0, .x2] .x6 (lbBody g))

/-! ## `normLt` -/

def nlBody : List Instr :=
  [.ldr .w .x12 .x0 0, .sub .x .x13 .x12 .x1, .sub .x .x14 .x9 .x12, .sub .x .x14 .x14 .x1,
    .logic .orr .x .x13 .x13 .x14, .logic .and .x .x10 .x10 .x13]

def normLt : Prog isa :=
  .seq (.block ([.addImm .w .x1 .x1 0] ++ movW .x9 (BitVec.ofNat 32 qNat) ++
      [.movz .x .x10 0 0, .subImm .x .x10 .x10 1]))
    (.seq (mapLoop [.x0] .x11 nlBody) (.block [.lsr .x .x0 .x10 63]))

/-! ## `makeHint` -/

def mhBody (g : Nat) : List Instr :=
  [.ldr .w .x11 .x1 0] ++ hb g .x12 .x11 .x13 .x5 .x6 ++
    [.ldr .w .x14 .x0 0, .add .x .x11 .x11 .x14] ++ csub .x11 .x13 .x9 ++ hb g .x14 .x11 .x13 .x5 .x6 ++
    [.logic .eor .x .x14 .x14 .x12, .addImm .x .x14 .x14 63, .lsr .x .x14 .x14 6, .str .w .x14 .x3 0,
      .add .x .x8 .x8 .x14]

/-- `M`, `2^(S-1)`, `q`, and the count of 1s. -/
def mhConsts (g : Nat) : List Instr :=
  hbConsts g .x5 .x6 ++ movW .x9 (BitVec.ofNat 32 qNat) ++ [.movz .x .x8 0 0]

def makeHint : Prog isa :=
  zext .x2 <| .seq (onGamma .x2 .x4 fun g => .seq (.block (mhConsts g)) (mapLoop [.x0, .x1, .x3] .x7 (mhBody g)))
    (.block [mov .x0 .x8])

/-! ## `useHint` -/

def uhBody (g : Nat) : List Instr :=
  [.ldr .w .x11 .x1 0] ++ hbRaw g .x12 .x11 .x5 .x6 ++
    [.mul .x .x13 .x12 .x7, .sub .x .x13 .x13 .x11, .lsr .x .x13 .x13 63, .lsl .x .x13 .x13 1,
      .subImm .x .x13 .x13 1, .ldr .w .x14 .x0 0, .sub .x .x14 .x9 .x14, .lsr .x .x14 .x14 63,
      .mul .x .x13 .x13 .x14, .add .x .x13 .x13 .x12, .addImm .x .x13 .x13 (dMod g)] ++
    csubR .x13 .x14 .x10 ++ csubR .x13 .x14 .x10 ++ [.str .w .x13 .x3 0]

/-- `M`, `2^(S-1)`, `2γ₂`, zero and `m`. -/
def uhConsts (g : Nat) : List Instr :=
  hbConsts g .x5 .x6 ++ movW .x7 (BitVec.ofNat 32 (2 * g)) ++
    [.movz .x .x9 0 0, .movz .x .x10 (BitVec.ofNat 16 (dMod g)) 0]

def useHint : Prog isa :=
  zext .x2 <| onGamma .x2 .x4 fun g => .seq (.block (uhConsts g)) (mapLoop [.x0, .x1, .x3] .x8 (uhBody g))

end VG.Impl.MlDsa.AArch64.Round
