import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Weierstrass.Rcb

/-!
# Polynomial identities of the complete addition formulas

Over any commutative ring, for points of `y² = x³ + a x + b`: `rcbAdd` is
symmetric in its two points and bihomogeneous of bidegree `(2, 2)`, it maps
`(0 : Y₁ : 0)` and `(X₂ : Y₂ : Z₂)` to a multiple of `(X₂ : Y₂ : Z₂)`, and on
points with `Z = 1` its output is, modulo the curve equations, a multiple of
the affine sum: of the chord's sum for `x₁ ≠ x₂` (scaled by `d = x₂ - x₁`),
of the tangent's for doubling (scaled by `2y`), and `(0 : Y₃ : 0)` for
`P + (-P)`. The coefficients of the curve equations were found by
polynomial division (computer algebra) and are checked by
`linear_combination`.
-/

namespace VG.Proof.Weierstrass

variable {F : Type*} [CommRing F]

theorem rcbAdd_comm (a b3 X1 Y1 Z1 X2 Y2 Z2 : F) :
    rcbAdd a b3 X1 Y1 Z1 X2 Y2 Z2 = rcbAdd a b3 X2 Y2 Z2 X1 Y1 Z1 := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem rcbAdd_scale (a b3 x1 y1 Z1 x2 y2 Z2 : F) :
    rcbAdd a b3 (x1 * Z1) (y1 * Z1) Z1 (x2 * Z2) (y2 * Z2) Z2 =
      (Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).1,
        Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).2.1,
        Z1 ^ 2 * Z2 ^ 2 * (rcbAdd a b3 x1 y1 1 x2 y2 1).2.2) := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- `O + Q`, with `O = (0 : Y₁ : 0)`. -/
theorem rcbAdd_zero_left (a b3 Y1 X2 Y2 Z2 : F) :
    rcbAdd a b3 0 Y1 0 X2 Y2 Z2 = (Y1 ^ 2 * Y2 * X2, Y1 ^ 2 * Y2 * Y2, Y1 ^ 2 * Y2 * Z2) := by
  simp only [rcbAdd, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem rcbAdd_neg_x (a b x y : F) : (rcbAdd a (3 * b) x y 1 x (-y) 1).1 = 0 := by
  simp only [rcbAdd]
  ring

theorem rcbAdd_neg_z (a b x y : F) : (rcbAdd a (3 * b) x y 1 x (-y) 1).2.2 = 0 := by
  simp only [rcbAdd]
  ring

section
variable {a b x1 y1 x2 y2 : F} (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
  (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b)
include h1 h2

/-- `Z₃` is `d³` times the `y`-coordinate of `P - Q`. -/
theorem rcbAdd_chord_z : (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 =
    (-y2 - y1) * ((x2 - x1) ^ 2 * x1 - ((-y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) -
      y1 * (x2 - x1) ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-y1 - 2*y2) * h1 + (-2*y1 - y2) * h2

theorem rcbAdd_chord_x : (x2 - x1) ^ 2 * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).1 =
    ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-a*x1*y1 - a*x1*y2 - 2*a*x2*y1 + 3*a*x2*y2 - 3*b*y1 + 2*b*y2 - 
    3*x1^2*x2*y2 - 3*x1*x2^2*y1 + 3*x1*x2^2*y2 + 2*x2^3*y2 - y1^2*y2 + y1*y2^2 + 
    y2^3) * h1 + (4*a*x1*y1 - a*x1*y2 - a*x2*y1 - a*x2*y2 + 3*b*y1 - 2*b*y2 + 3*x1^3*y1 + 
    x1^3*y2 + 3*x1^2*x2*y1 - 3*x1^2*x2*y2 - 3*x1*x2^2*y1 - y1*y2^2) * h2

theorem rcbAdd_chord_y : (x2 - x1) ^ 3 * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.1 =
    ((y2 - y1) * ((x2 - x1) ^ 2 * x1 - ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) -
      y1 * (x2 - x1) ^ 3) * (rcbAdd a (3 * b) x1 y1 1 x2 y2 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-a^2*x1^2 - 2*a^2*x1*x2 - 4*a*b*x1 - 2*a*b*x2 - 6*a*x1^2*x2^2 - 
    4*a*x1*x2^3 - a*x1*y1^2 + 5*a*x1*y2^2 + 4*a*x2^4 - 2*a*x2*y1^2 + 5*a*x2*y1*y2 - 
    3*a*x2*y2^2 - 3*b^2 - 12*b*x1*x2^2 + 6*b*x2^3 - 3*b*y1^2 + 5*b*y1*y2 + 2*b*y2^2 - 
    9*x1^2*x2^4 - 3*x1^2*x2*y1*y2 + 15*x1^2*x2*y2^2 + 6*x1*x2^5 - 3*x1*x2^2*y1^2 + 
    6*x1*x2^2*y1*y2 - 15*x1*x2^2*y2^2 + 2*x2^3*y1*y2 + 2*x2^3*y2^2 - y1^3*y2 + 
    2*y1^2*y2^2 - 2*y2^4) * h1 + (5*a^2*x1^2 - 3*a^2*x1*x2 + a^2*x2^2 + 7*a*b*x1 - 
    a*b*x2 + a*x1^4 + 14*a*x1^3*x2 - 9*a*x1^2*x2^2 - 5*a*x1*y1*y2 + a*x2*y2^2 + 3*b^2 - 
    6*b*x1^3 + 27*b*x1^2*x2 - 15*b*x1*x2^2 - 5*b*y1*y2 + b*y2^2 + 9*x1^5*x2 - 
    6*x1^4*x2^2 - 2*x1^3*y1*y2 - 2*x1^3*y2^2 - 6*x1^2*x2*y1*y2 + 3*x1^2*x2*y2^2 + 
    3*x1*x2^2*y1*y2 + y1*y2^3) * h2

end

section
variable {a b x y : F} (h : y ^ 2 = x ^ 3 + a * x + b)
include h

theorem rcbAdd_tangent_z : (rcbAdd a (3 * b) x y 1 x y 1).2.2 = 8 * y ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-6*y) * h

theorem rcbAdd_tangent_x : (2 * y) ^ 2 * (rcbAdd a (3 * b) x y 1 x y 1).1 =
    ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (6*a^2*y + 36*a*x^2*y + 54*x^4*y + 24*x*y^3) * h

theorem rcbAdd_tangent_y : (2 * y) ^ 3 * (rcbAdd a (3 * b) x y 1 x y 1).2.1 =
    ((3 * x ^ 2 + a) * ((2 * y) ^ 2 * x - ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2)) -
      y * (2 * y) ^ 3) * (rcbAdd a (3 * b) x y 1 x y 1).2.2 := by
  simp only [rcbAdd]
  linear_combination (-6*a^3*y - 54*a^2*x^2*y - 162*a*x^4*y + 48*a*x*y^3 + 72*b*y^3 - 
    162*x^6*y + 24*y^5) * h

/-- `Y₃` is `(2y)³` times the `y`-coordinate of `2P`. -/
theorem rcbAdd_neg_y : (rcbAdd a (3 * b) x y 1 x (-y) 1).2.1 =
    (3 * x ^ 2 + a) * ((2 * y) ^ 2 * x - ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2)) -
      y * (2 * y) ^ 3 := by
  simp only [rcbAdd]
  linear_combination (-3*a*x + 9*b - 27*x^3 + 9*y^2) * h

end

end VG.Proof.Weierstrass
