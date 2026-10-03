import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The arithmetic of `Neon.mul2`'s products

Untrusted: everything here is checked by Lean. Coefficient `q` of the product
of two eight-limb halves is `cv x y q`; Karatsuba's identity for `φ = x⁸`
(`x = 2²⁸`) combines three of them into sixteen coefficients `kara a b k`,
which represent the product of the sixteen-limb operands modulo
`p = x¹⁶ - x⁸ - 1` (`kara_val`), and are at most the sum of their positive
terms (`kara_nonneg`, `kara_le`).
-/

namespace VG.Proof.Curve448.AArch64.Neon

/-- Coefficient `q` of the product of the eight-limb halves `x` and `y`. -/
def cv (x y : Nat → Nat) : Nat → Nat
  | 0 => x 0 * y 0
  | 1 => x 0 * y 1 + x 1 * y 0
  | 2 => x 0 * y 2 + x 1 * y 1 + x 2 * y 0
  | 3 => x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0
  | 4 => x 0 * y 4 + x 1 * y 3 + x 2 * y 2 + x 3 * y 1 + x 4 * y 0
  | 5 => x 0 * y 5 + x 1 * y 4 + x 2 * y 3 + x 3 * y 2 + x 4 * y 1 + x 5 * y 0
  | 6 => x 0 * y 6 + x 1 * y 5 + x 2 * y 4 + x 3 * y 3 + x 4 * y 2 + x 5 * y 1 + x 6 * y 0
  | 7 => x 0 * y 7 + x 1 * y 6 + x 2 * y 5 + x 3 * y 4 + x 4 * y 3 + x 5 * y 2 + x 6 * y 1 + x 7 * y 0
  | 8 => x 1 * y 7 + x 2 * y 6 + x 3 * y 5 + x 4 * y 4 + x 5 * y 3 + x 6 * y 2 + x 7 * y 1
  | 9 => x 2 * y 7 + x 3 * y 6 + x 4 * y 5 + x 5 * y 4 + x 6 * y 3 + x 7 * y 2
  | 10 => x 3 * y 7 + x 4 * y 6 + x 5 * y 5 + x 6 * y 4 + x 7 * y 3
  | 11 => x 4 * y 7 + x 5 * y 6 + x 6 * y 5 + x 7 * y 4
  | 12 => x 5 * y 7 + x 6 * y 6 + x 7 * y 5
  | 13 => x 6 * y 7 + x 7 * y 6
  | 14 => x 7 * y 7
  | _ => 0

/-- The halves of a sixteen-limb operand, and their sum. -/
def hl (a : Nat → Nat) (h : Nat) (i : Nat) : Nat :=
  match h with
  | 0 => a i
  | 1 => a (8 + i)
  | _ => a i + a (8 + i)

abbrev S (a b : Nat → Nat) (q : Nat) : Nat := cv (hl a 0) (hl b 0) q
abbrev T (a b : Nat → Nat) (q : Nat) : Nat := cv (hl a 1) (hl b 1) q
abbrev U (a b : Nat → Nat) (q : Nat) : Nat := cv (hl a 2) (hl b 2) q

/-- Karatsuba's coefficients. -/
def kara (a b : Nat → Nat) (k : Nat) : Int :=
  if k < 8 then (S a b k : Int) + T a b k + U a b (k + 8) - S a b (k + 8)
  else (T a b k : Int) + U a b (k - 8) + U a b k - S a b (k - 8)

theorem conv8 (X x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : Int) :
    (x0 * X ^ 0 + x1 * X ^ 1 + x2 * X ^ 2 + x3 * X ^ 3 + x4 * X ^ 4 + x5 * X ^ 5 + x6 * X ^ 6 + x7 * X ^ 7) * (y0 * X ^ 0 + y1 * X ^ 1 + y2 * X ^ 2 + y3 * X ^ 3 + y4 * X ^ 4 + y5 * X ^ 5 + y6 * X ^ 6 + y7 * X ^ 7) = (x0 * y0) * X ^ 0 + (x0 * y1 + x1 * y0) * X ^ 1 + (x0 * y2 + x1 * y1 + x2 * y0) * X ^ 2 + (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0) * X ^ 3 + (x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0) * X ^ 4 + (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0) * X ^ 5 + (x0 * y6 + x1 * y5 + x2 * y4 + x3 * y3 + x4 * y2 + x5 * y1 + x6 * y0) * X ^ 6 + (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0) * X ^ 7 + (x1 * y7 + x2 * y6 + x3 * y5 + x4 * y4 + x5 * y3 + x6 * y2 + x7 * y1) * X ^ 8 + (x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2) * X ^ 9 + (x3 * y7 + x4 * y6 + x5 * y5 + x6 * y4 + x7 * y3) * X ^ 10 + (x4 * y7 + x5 * y6 + x6 * y5 + x7 * y4) * X ^ 11 + (x5 * y7 + x6 * y6 + x7 * y5) * X ^ 12 + (x6 * y7 + x7 * y6) * X ^ 13 + (x7 * y7) * X ^ 14 := by
  ring

theorem kara_comb (X S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14 : Int) :
    (S0 * X ^ 0 + S1 * X ^ 1 + S2 * X ^ 2 + S3 * X ^ 3 + S4 * X ^ 4 + S5 * X ^ 5 + S6 * X ^ 6 + S7 * X ^ 7 + S8 * X ^ 8 + S9 * X ^ 9 + S10 * X ^ 10 + S11 * X ^ 11 + S12 * X ^ 12 + S13 * X ^ 13 + S14 * X ^ 14) + X ^ 8 * ((U0 * X ^ 0 + U1 * X ^ 1 + U2 * X ^ 2 + U3 * X ^ 3 + U4 * X ^ 4 + U5 * X ^ 5 + U6 * X ^ 6 + U7 * X ^ 7 + U8 * X ^ 8 + U9 * X ^ 9 + U10 * X ^ 10 + U11 * X ^ 11 + U12 * X ^ 12 + U13 * X ^ 13 + U14 * X ^ 14) - (S0 * X ^ 0 + S1 * X ^ 1 + S2 * X ^ 2 + S3 * X ^ 3 + S4 * X ^ 4 + S5 * X ^ 5 + S6 * X ^ 6 + S7 * X ^ 7 + S8 * X ^ 8 + S9 * X ^ 9 + S10 * X ^ 10 + S11 * X ^ 11 + S12 * X ^ 12 + S13 * X ^ 13 + S14 * X ^ 14) - (T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14)) + X ^ 16 * (T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14) - ((S0 + T0 + U8 - S8) * X ^ 0 + (S1 + T1 + U9 - S9) * X ^ 1 + (S2 + T2 + U10 - S10) * X ^ 2 + (S3 + T3 + U11 - S11) * X ^ 3 + (S4 + T4 + U12 - S12) * X ^ 4 + (S5 + T5 + U13 - S13) * X ^ 5 + (S6 + T6 + U14 - S14) * X ^ 6 + (S7 + T7 + 0 - 0) * X ^ 7 + (T8 + U0 + U8 - S0) * X ^ 8 + (T9 + U1 + U9 - S1) * X ^ 9 + (T10 + U2 + U10 - S2) * X ^ 10 + (T11 + U3 + U11 - S3) * X ^ 11 + (T12 + U4 + U12 - S4) * X ^ 12 + (T13 + U5 + U13 - S5) * X ^ 13 + (T14 + U6 + U14 - S6) * X ^ 14 + (0 + U7 + 0 - S7) * X ^ 15) =
      (X ^ 16 - X ^ 8 - 1) * ((T0 * X ^ 0 + T1 * X ^ 1 + T2 * X ^ 2 + T3 * X ^ 3 + T4 * X ^ 4 + T5 * X ^ 5 + T6 * X ^ 6 + T7 * X ^ 7 + T8 * X ^ 8 + T9 * X ^ 9 + T10 * X ^ 10 + T11 * X ^ 11 + T12 * X ^ 12 + T13 * X ^ 13 + T14 * X ^ 14) + (U8 * X ^ 0 + U9 * X ^ 1 + U10 * X ^ 2 + U11 * X ^ 3 + U12 * X ^ 4 + U13 * X ^ 5 + U14 * X ^ 6) - (S8 * X ^ 0 + S9 * X ^ 1 + S10 * X ^ 2 + S11 * X ^ 3 + S12 * X ^ 4 + S13 * X ^ 5 + S14 * X ^ 6)) := by
  ring

theorem halves (X : Int) (a : Nat → Nat) : (a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15 = ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7) + X ^ 8 * ((a 8 : Int) * X ^ 0 + (a 9 : Int) * X ^ 1 + (a 10 : Int) * X ^ 2 + (a 11 : Int) * X ^ 3 + (a 12 : Int) * X ^ 4 + (a 13 : Int) * X ^ 5 + (a 14 : Int) * X ^ 6 + (a 15 : Int) * X ^ 7) := by ring

theorem prodS (X : Int) (a b : Nat → Nat) : ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7) = (S a b 0 : Int) * X ^ 0 + (S a b 1 : Int) * X ^ 1 + (S a b 2 : Int) * X ^ 2 + (S a b 3 : Int) * X ^ 3 + (S a b 4 : Int) * X ^ 4 + (S a b 5 : Int) * X ^ 5 + (S a b 6 : Int) * X ^ 6 + (S a b 7 : Int) * X ^ 7 + (S a b 8 : Int) * X ^ 8 + (S a b 9 : Int) * X ^ 9 + (S a b 10 : Int) * X ^ 10 + (S a b 11 : Int) * X ^ 11 + (S a b 12 : Int) * X ^ 12 + (S a b 13 : Int) * X ^ 13 + (S a b 14 : Int) * X ^ 14 := by
  rw [conv8 X (a 0 : Int) (a 1 : Int) (a 2 : Int) (a 3 : Int) (a 4 : Int) (a 5 : Int) (a 6 : Int) (a 7 : Int) (b 0 : Int) (b 1 : Int) (b 2 : Int) (b 3 : Int) (b 4 : Int) (b 5 : Int) (b 6 : Int) (b 7 : Int)]
  simp only [S, cv, hl]; push_cast; ring

theorem prodT (X : Int) (a b : Nat → Nat) : ((a 8 : Int) * X ^ 0 + (a 9 : Int) * X ^ 1 + (a 10 : Int) * X ^ 2 + (a 11 : Int) * X ^ 3 + (a 12 : Int) * X ^ 4 + (a 13 : Int) * X ^ 5 + (a 14 : Int) * X ^ 6 + (a 15 : Int) * X ^ 7) * ((b 8 : Int) * X ^ 0 + (b 9 : Int) * X ^ 1 + (b 10 : Int) * X ^ 2 + (b 11 : Int) * X ^ 3 + (b 12 : Int) * X ^ 4 + (b 13 : Int) * X ^ 5 + (b 14 : Int) * X ^ 6 + (b 15 : Int) * X ^ 7) = (T a b 0 : Int) * X ^ 0 + (T a b 1 : Int) * X ^ 1 + (T a b 2 : Int) * X ^ 2 + (T a b 3 : Int) * X ^ 3 + (T a b 4 : Int) * X ^ 4 + (T a b 5 : Int) * X ^ 5 + (T a b 6 : Int) * X ^ 6 + (T a b 7 : Int) * X ^ 7 + (T a b 8 : Int) * X ^ 8 + (T a b 9 : Int) * X ^ 9 + (T a b 10 : Int) * X ^ 10 + (T a b 11 : Int) * X ^ 11 + (T a b 12 : Int) * X ^ 12 + (T a b 13 : Int) * X ^ 13 + (T a b 14 : Int) * X ^ 14 := by
  rw [conv8 X (a 8 : Int) (a 9 : Int) (a 10 : Int) (a 11 : Int) (a 12 : Int) (a 13 : Int) (a 14 : Int) (a 15 : Int) (b 8 : Int) (b 9 : Int) (b 10 : Int) (b 11 : Int) (b 12 : Int) (b 13 : Int) (b 14 : Int) (b 15 : Int)]
  simp only [T, cv, hl]; push_cast; ring

theorem prodU (X : Int) (a b : Nat → Nat) : (((a 0 + a 8) : Int) * X ^ 0 + ((a 1 + a 9) : Int) * X ^ 1 + ((a 2 + a 10) : Int) * X ^ 2 + ((a 3 + a 11) : Int) * X ^ 3 + ((a 4 + a 12) : Int) * X ^ 4 + ((a 5 + a 13) : Int) * X ^ 5 + ((a 6 + a 14) : Int) * X ^ 6 + ((a 7 + a 15) : Int) * X ^ 7) * (((b 0 + b 8) : Int) * X ^ 0 + ((b 1 + b 9) : Int) * X ^ 1 + ((b 2 + b 10) : Int) * X ^ 2 + ((b 3 + b 11) : Int) * X ^ 3 + ((b 4 + b 12) : Int) * X ^ 4 + ((b 5 + b 13) : Int) * X ^ 5 + ((b 6 + b 14) : Int) * X ^ 6 + ((b 7 + b 15) : Int) * X ^ 7) = (U a b 0 : Int) * X ^ 0 + (U a b 1 : Int) * X ^ 1 + (U a b 2 : Int) * X ^ 2 + (U a b 3 : Int) * X ^ 3 + (U a b 4 : Int) * X ^ 4 + (U a b 5 : Int) * X ^ 5 + (U a b 6 : Int) * X ^ 6 + (U a b 7 : Int) * X ^ 7 + (U a b 8 : Int) * X ^ 8 + (U a b 9 : Int) * X ^ 9 + (U a b 10 : Int) * X ^ 10 + (U a b 11 : Int) * X ^ 11 + (U a b 12 : Int) * X ^ 12 + (U a b 13 : Int) * X ^ 13 + (U a b 14 : Int) * X ^ 14 := by
  rw [conv8 X ((a 0 + a 8) : Int) ((a 1 + a 9) : Int) ((a 2 + a 10) : Int) ((a 3 + a 11) : Int) ((a 4 + a 12) : Int) ((a 5 + a 13) : Int) ((a 6 + a 14) : Int) ((a 7 + a 15) : Int) ((b 0 + b 8) : Int) ((b 1 + b 9) : Int) ((b 2 + b 10) : Int) ((b 3 + b 11) : Int) ((b 4 + b 12) : Int) ((b 5 + b 13) : Int) ((b 6 + b 14) : Int) ((b 7 + b 15) : Int)]
  simp only [U, cv, hl]; push_cast; ring

theorem kara_sum (X : Int) (a b : Nat → Nat) :
    ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7 + (b 8 : Int) * X ^ 8 + (b 9 : Int) * X ^ 9 + (b 10 : Int) * X ^ 10 + (b 11 : Int) * X ^ 11 + (b 12 : Int) * X ^ 12 + (b 13 : Int) * X ^ 13 + (b 14 : Int) * X ^ 14 + (b 15 : Int) * X ^ 15) - (kara a b 0 * X ^ 0 + kara a b 1 * X ^ 1 + kara a b 2 * X ^ 2 + kara a b 3 * X ^ 3 + kara a b 4 * X ^ 4 + kara a b 5 * X ^ 5 + kara a b 6 * X ^ 6 + kara a b 7 * X ^ 7 + kara a b 8 * X ^ 8 + kara a b 9 * X ^ 9 + kara a b 10 * X ^ 10 + kara a b 11 * X ^ 11 + kara a b 12 * X ^ 12 + kara a b 13 * X ^ 13 + kara a b 14 * X ^ 14 + kara a b 15 * X ^ 15) =
      (X ^ 16 - X ^ 8 - 1) * (((T a b 0 : Int) * X ^ 0 + (T a b 1 : Int) * X ^ 1 + (T a b 2 : Int) * X ^ 2 + (T a b 3 : Int) * X ^ 3 + (T a b 4 : Int) * X ^ 4 + (T a b 5 : Int) * X ^ 5 + (T a b 6 : Int) * X ^ 6 + (T a b 7 : Int) * X ^ 7 + (T a b 8 : Int) * X ^ 8 + (T a b 9 : Int) * X ^ 9 + (T a b 10 : Int) * X ^ 10 + (T a b 11 : Int) * X ^ 11 + (T a b 12 : Int) * X ^ 12 + (T a b 13 : Int) * X ^ 13 + (T a b 14 : Int) * X ^ 14) + ((U a b 8 : Int) * X ^ 0 + (U a b 9 : Int) * X ^ 1 + (U a b 10 : Int) * X ^ 2 + (U a b 11 : Int) * X ^ 3 + (U a b 12 : Int) * X ^ 4 + (U a b 13 : Int) * X ^ 5 + (U a b 14 : Int) * X ^ 6) - ((S a b 8 : Int) * X ^ 0 + (S a b 9 : Int) * X ^ 1 + (S a b 10 : Int) * X ^ 2 + (S a b 11 : Int) * X ^ 3 + (S a b 12 : Int) * X ^ 4 + (S a b 13 : Int) * X ^ 5 + (S a b 14 : Int) * X ^ 6)) := by
  have hA := halves X a
  have hB := halves X b
  have h1 := prodS X a b
  have h2 := prodT X a b
  have h3 := prodU X a b
  have hk := kara_comb X (S a b 0) (S a b 1) (S a b 2) (S a b 3) (S a b 4) (S a b 5) (S a b 6) (S a b 7) (S a b 8) (S a b 9) (S a b 10) (S a b 11) (S a b 12) (S a b 13) (S a b 14) (T a b 0) (T a b 1) (T a b 2) (T a b 3) (T a b 4) (T a b 5) (T a b 6) (T a b 7) (T a b 8) (T a b 9) (T a b 10) (T a b 11) (T a b 12) (T a b 13) (T a b 14) (U a b 0) (U a b 1) (U a b 2) (U a b 3) (U a b 4) (U a b 5) (U a b 6) (U a b 7) (U a b 8) (U a b 9) (U a b 10) (U a b 11) (U a b 12) (U a b 13) (U a b 14)
  have e15 : S a b 15 = 0 ∧ T a b 15 = 0 ∧ U a b 15 = 0 := ⟨rfl, rfl, rfl⟩
  simp only [kara, show (0 : Nat) < 8 by decide, show (1 : Nat) < 8 by decide, show (2 : Nat) < 8 by decide,
    show (3 : Nat) < 8 by decide, show (4 : Nat) < 8 by decide, show (5 : Nat) < 8 by decide,
    show (6 : Nat) < 8 by decide, show (7 : Nat) < 8 by decide, show ¬ (8 : Nat) < 8 by decide,
    show ¬ (9 : Nat) < 8 by decide, show ¬ (10 : Nat) < 8 by decide, show ¬ (11 : Nat) < 8 by decide,
    show ¬ (12 : Nat) < 8 by decide, show ¬ (13 : Nat) < 8 by decide, show ¬ (14 : Nat) < 8 by decide,
    show ¬ (15 : Nat) < 8 by decide, ite_true, ite_false, Nat.reduceAdd, Nat.reduceSub, e15.1, e15.2.1, e15.2.2,
    Nat.cast_zero] at hk ⊢
  rw [hA, hB]
  linear_combination hk + h1 * (1 - X ^ 8) + h2 * (X ^ 16 - X ^ 8) + h3 * X ^ 8

theorem cv_mono {x y x' y' : Nat → Nat} (hx : ∀ i < 8, x i ≤ x' i) (hy : ∀ i < 8, y i ≤ y' i) (q : Nat) :
    cv x y q ≤ cv x' y' q := by
  have m : ∀ i j, i < 8 → j < 8 → x i * y j ≤ x' i * y' j := fun i j hi hj =>
    Nat.mul_le_mul (hx i hi) (hy j hj)
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q
  all_goals simp only [cv]
  all_goals first
    | exact Nat.le_refl _
    | (repeat' apply Nat.add_le_add) <;> exact m _ _ (by decide) (by decide)

theorem S_le_U (a b : Nat → Nat) (q : Nat) : S a b q ≤ U a b q :=
  cv_mono (fun _ _ => Nat.le_add_right _ _) (fun _ _ => Nat.le_add_right _ _) q

theorem kara_nonneg (a b : Nat → Nat) (k : Nat) : 0 ≤ kara a b k := by
  unfold kara
  split
  · have := S_le_U a b (k + 8); omega
  · have := S_le_U a b (k - 8); omega

/-- Bounds on the radix-2²⁸ limbs of an operand below `Ib` in radix 2⁵⁶. -/
def lmax (k : Nat) : Nat := if k % 2 = 0 then 2 ^ 28 - 1 else 3 * 2 ^ 28

theorem kara_le {a b : Nat → Nat} (ha : ∀ k < 16, a k ≤ lmax k) (hb : ∀ k < 16, b k ≤ lmax k) {k : Nat}
    (hk : k < 16) : kara a b k < 2 ^ 64 - 2 ^ 40 := by
  have hm : ∀ h < 3, ∀ i < 8, hl a h i ≤ hl lmax h i ∧ hl b h i ≤ hl lmax h i := by
    intro h hh i hi
    rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega) with rfl | rfl | rfl <;> simp only [hl]
    · exact ⟨ha i (by omega), hb i (by omega)⟩
    · exact ⟨ha _ (by omega), hb _ (by omega)⟩
    · exact ⟨Nat.add_le_add (ha i (by omega)) (ha _ (by omega)), Nat.add_le_add (hb i (by omega)) (hb _ (by omega))⟩
  have bS : ∀ q, S a b q ≤ S lmax lmax q := fun q =>
    cv_mono (fun i hi => (hm 0 (by decide) i hi).1) (fun i hi => (hm 0 (by decide) i hi).2) q
  have bT : ∀ q, T a b q ≤ T lmax lmax q := fun q =>
    cv_mono (fun i hi => (hm 1 (by decide) i hi).1) (fun i hi => (hm 1 (by decide) i hi).2) q
  have bU : ∀ q, U a b q ≤ U lmax lmax q := fun q =>
    cv_mono (fun i hi => (hm 2 (by decide) i hi).1) (fun i hi => (hm 2 (by decide) i hi).2) q
  have num : ∀ k < 8, S lmax lmax k + T lmax lmax k + U lmax lmax (k + 8) < 2 ^ 64 - 2 ^ 40 ∧
      T lmax lmax (k + 8) + U lmax lmax k + U lmax lmax (k + 8) < 2 ^ 64 - 2 ^ 40 := by decide
  unfold kara
  split
  · have := num k (by omega); have := bS k; have := bT k; have := bU (k + 8); omega
  · have := num (k - 8) (by omega); have := bT k; have := bU (k - 8); have := bU k
    rw [show k - 8 + 8 = k by omega] at *
    omega

end VG.Proof.Curve448.AArch64.Neon
