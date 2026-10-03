import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Weierstrass.RcbIdent

/-!
# The affine group law and the complete formulas over a field

Over a field `F`, for the curve `y² = x³ + a x + b`: the chord and tangent
constructions give points of the curve (Mathlib's
`WeierstrassCurve.Affine.equation_add`, for `a₁ = a₂ = a₃ = 0`), and, if no
point of the curve has `y = 0` (no point of order 2) and `2 ≠ 0`, `rcbAdd` on
points with `Z = 1` gives a nonzero multiple of their sum: of the chord's sum
for `x₁ ≠ x₂`, of the tangent's for `P = Q`, and `(0 : Y₃ : 0)` with
`Y₃ ≠ 0` for `Q = -P`. The slopes are any `l` with `l (x₂ - x₁) = y₂ - y₁`
(or `l · 2y = 3x² + a`), so that callers can give them as quotients.
-/

namespace VG.Proof.Weierstrass

variable {F : Type*} [Field F] {a b : F}

/-- `y² = x³ + a x + b` as a Weierstrass curve. -/
def wc (a b : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

theorem wc_equation {x y : F} : (wc a b).Equation x y ↔ y ^ 2 = x ^ 3 + a * x + b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [wc, zero_mul, add_zero]

section
open WeierstrassCurve.Affine

/-- The chord through two points of the curve meets it again in a point
whose reflection is on the curve. -/
theorem chord_on {x1 y1 x2 y2 l : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 ≠ x2) (hl : l * (x2 - x1) = y2 - y1) :
    (l * (x1 - (l * l - x1 - x2)) - y1) ^ 2 =
      (l * l - x1 - x2) ^ 3 + a * (l * l - x1 - x2) + b := by
  classical
  have e := (wc a b).equation_add (wc_equation.mpr h1) (wc_equation.mpr h2)
    (fun h => hx h.1)
  have hs : (wc a b).slope x1 x2 y1 y2 = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
    linear_combination hl
  rw [hs, wc_equation] at e
  simp only [addY, negY, negAddY, addX, wc, zero_mul, sub_zero, add_zero] at e
  linear_combination e

/-- The tangent at a point of the curve with `2y ≠ 0` meets it again in a
point whose reflection is on the curve. -/
theorem tangent_on {x y l : F} (h : y ^ 2 = x ^ 3 + a * x + b) (hy : 2 * y ≠ 0)
    (hl : l * (2 * y) = 3 * x ^ 2 + a) :
    (l * (x - (l * l - 2 * x)) - y) ^ 2 = (l * l - 2 * x) ^ 3 + a * (l * l - 2 * x) + b := by
  classical
  have hn : y ≠ (wc a b).negY x y := by
    simp only [negY, wc, zero_mul, sub_zero]
    intro h'; apply hy; linear_combination h'
  have e := (wc a b).equation_add (wc_equation.mpr h) (wc_equation.mpr h)
    (fun h' => hn h'.2)
  have hs : (wc a b).slope x x y y = l := by
    have hd : y - (wc a b).negY x y ≠ 0 := sub_ne_zero.mpr hn
    rw [slope_of_Y_ne rfl hn, div_eq_iff hd]
    simp only [negY, wc, zero_mul, sub_zero, mul_zero, add_zero]
    linear_combination -hl
  rw [hs, wc_equation] at e
  simp only [addY, negY, negAddY, addX, wc, zero_mul, sub_zero, add_zero] at e
  linear_combination e

end

/-! ## `rcbAdd` on points with `Z = 1` -/

section
variable (ht : ∀ x : F, x ^ 3 + a * x + b ≠ 0)
include ht

theorem y_ne_zero {x y : F} (h : y ^ 2 = x ^ 3 + a * x + b) : y ≠ 0 := by
  rintro rfl; exact ht x (by linear_combination -h)

/-- For `x₁ ≠ x₂`: a nonzero multiple of the chord's sum. -/
theorem rcbAdd_chord {x1 y1 x2 y2 l : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) (hx : x1 ≠ x2) (hl : l * (x2 - x1) = y2 - y1) :
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 ≠ 0 ∧
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).1 =
      (l * l - x1 - x2) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 ∧
    (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.1 =
      (l * (x1 - (l * l - x1 - x2)) - y1) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  have hd : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨?_, ?_, ?_⟩
  · -- `Z₃ = d³ · y(P - Q)`, and `P - Q` is a point of the curve.
    have h2' : (-y2) ^ 2 = x2 ^ 3 + a * x2 + b := by linear_combination h2
    have hl' : (-y2 - y1) / (x2 - x1) * (x2 - x1) = -y2 - y1 := div_mul_cancel₀ _ hd
    have hon := chord_on h1 h2' hx hl'
    have hz := rcbAdd_chord_z h1 h2
    rw [← hl'] at hz
    rw [hz]
    intro h0
    have hy : (-y2 - y1) / (x2 - x1) * (x1 - ((-y2 - y1) / (x2 - x1) * ((-y2 - y1) / (x2 - x1)) -
        x1 - x2)) - y1 = 0 := by
      refine (mul_eq_zero.mp (?_ : (x2 - x1) ^ 3 * _ = 0)).resolve_left (pow_ne_zero 3 hd)
      linear_combination h0
    rw [hy] at hon
    exact y_ne_zero ht hon rfl
  · have e := rcbAdd_chord_x h1 h2
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 2 hd) ?_
    linear_combination e
  · have e := rcbAdd_chord_y h1 h2
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 3 hd) ?_
    linear_combination e

/-- For `P = Q`: a nonzero multiple of the tangent's sum. -/
theorem rcbAdd_tangent (h2 : (2 : F) ≠ 0) {x y l : F} (h : y ^ 2 = x ^ 3 + a * x + b)
    (hl : l * (2 * y) = 3 * x ^ 2 + a) :
    (rcbAdd a (3 * b) x y 1 x y 1).2.2 ≠ 0 ∧
    (rcbAdd a (3 * b) x y 1 x y 1).1 = (l * l - 2 * x) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 ∧
    (rcbAdd a (3 * b) x y 1 x y 1).2.1 =
      (l * (x - (l * l - 2 * x)) - y) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  have hy : 2 * y ≠ 0 := mul_ne_zero h2 (y_ne_zero ht h)
  refine ⟨?_, ?_, ?_⟩
  · rw [rcbAdd_tangent_z h, show (8 : F) * y ^ 3 = (2 * y) ^ 3 by ring]
    exact pow_ne_zero 3 hy
  · have e := rcbAdd_tangent_x h
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 2 hy) ?_
    linear_combination e
  · have e := rcbAdd_tangent_y h
    rw [← hl] at e
    refine mul_left_cancel₀ (pow_ne_zero 3 hy) ?_
    linear_combination e

/-- For `Q = -P`: `(0 : Y₃ : 0)` with `Y₃ ≠ 0` (`Y₃` is `(2y)³` times the
`y`-coordinate of `2P`). -/
theorem rcbAdd_neg (h2 : (2 : F) ≠ 0) {x y : F} (h : y ^ 2 = x ^ 3 + a * x + b) :
    (rcbAdd a (3 * b) x y 1 x (-y) 1).1 = 0 ∧ (rcbAdd a (3 * b) x y 1 x (-y) 1).2.1 ≠ 0 ∧
    (rcbAdd a (3 * b) x y 1 x (-y) 1).2.2 = 0 := by
  refine ⟨rcbAdd_neg_x a b x y, ?_, rcbAdd_neg_z a b x y⟩
  have hy : 2 * y ≠ 0 := mul_ne_zero h2 (y_ne_zero ht h)
  have hl : (3 * x ^ 2 + a) / (2 * y) * (2 * y) = 3 * x ^ 2 + a := div_mul_cancel₀ _ hy
  have hon := tangent_on h hy hl
  have e := rcbAdd_neg_y h
  rw [← hl] at e
  rw [e]
  intro h0
  have hy2 : (3 * x ^ 2 + a) / (2 * y) * (x - ((3 * x ^ 2 + a) / (2 * y) *
      ((3 * x ^ 2 + a) / (2 * y)) - 2 * x)) - y = 0 := by
    refine (mul_eq_zero.mp (?_ : (2 * y) ^ 3 * _ = 0)).resolve_left (pow_ne_zero 3 hy)
    linear_combination h0
  rw [hy2] at hon
  exact y_ne_zero ht hon rfl

end

end VG.Proof.Weierstrass
