import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The group law of a complete twisted Edwards curve with `a = -1`

Untrusted. Over any field `F` with `2 ≠ 0`, a square root of `-1` and a
nonsquare `d`, the curve `-x² + y² = 1 + d x² y²` with the addition law
of RFC 8032 §5.1.4 (in affine coordinates) is complete: the denominators
never vanish (Bernstein, Birkner, Joye, Lange and Peters, "Twisted Edwards
curves", Theorem 3.3). Closure and associativity are polynomial identities
modulo the curve equations, checked by `linear_combination` with the
quotients of dividing by them (Hales, "The group law for Edwards curves").
-/

namespace VG.Proof.Ed25519.Edwards

variable {F : Type*} [Field F]

/-- The curve `-x² + y² = 1 + d x² y²`. -/
def OnCurve (d x y : F) : Prop := -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

/-- What makes the addition law complete. -/
structure Params (d : F) : Prop where
  two : (2 : F) ≠ 0
  sqrtm1 : ∃ s : F, s ^ 2 = -1
  nonsq : ∀ r : F, r ^ 2 ≠ d

/-- The affine addition law (RFC 8032 §5.1.4, divided out). -/
def addX (d x1 y1 x2 y2 : F) : F := (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)

def addY (d x1 y1 x2 y2 : F) : F := (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)

section
variable {d x1 y1 x2 y2 : F}

theorem sq_ne_one (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    (d * x1 * x2 * y1 * y2) ^ 2 ≠ 1 := by
  intro he2
  obtain ⟨s, hs⟩ := hP.sqrtm1
  set e := d * x1 * x2 * y1 * y2 with he
  have e0 : e ≠ 0 := by rintro h; rw [h] at he2; simp at he2
  have hx1 : x1 ≠ 0 := by rintro rfl; apply e0; rw [he]; ring
  have hy1 : y1 ≠ 0 := by rintro rfl; apply e0; rw [he]; ring
  have hy2 : y2 ≠ 0 := by rintro rfl; apply e0; rw [he]; ring
  have key (σ : F) (hσ : σ ^ 2 = 1) :
      (s * x1 + σ * e * y1) ^ 2 = d * x1 ^ 2 * y1 ^ 2 * (s * x2 + σ * y2) ^ 2 := by
    unfold OnCurve at h1 h2
    calc (s * x1 + σ * e * y1) ^ 2
        = -x1 ^ 2 + y1 ^ 2 + 2 * s * σ * e * x1 * y1 := by
          linear_combination x1 ^ 2 * hs + y1 ^ 2 * e ^ 2 * hσ + y1 ^ 2 * he2
      _ = 1 + d * x1 ^ 2 * y1 ^ 2 + 2 * s * σ * e * x1 * y1 := by linear_combination h1
      _ = d * x1 ^ 2 * y1 ^ 2 * (1 + d * x2 ^ 2 * y2 ^ 2) + 2 * s * σ * x1 * y1 * e := by
          linear_combination (-(e + d * x1 * x2 * y1 * y2)) * he - he2
      _ = d * x1 ^ 2 * y1 ^ 2 * (-x2 ^ 2 + y2 ^ 2) + 2 * s * σ * d * x1 ^ 2 * y1 ^ 2 * x2 * y2 := by
          linear_combination (-(d * x1 ^ 2 * y1 ^ 2)) * h2 + 2 * s * σ * x1 * y1 * he
      _ = d * x1 ^ 2 * y1 ^ 2 * (s * x2 + σ * y2) ^ 2 := by
          linear_combination (-(d * x1 ^ 2 * y1 ^ 2 * x2 ^ 2)) * hs - d * x1 ^ 2 * y1 ^ 2 * y2 ^ 2 * hσ
  have sq (σ : F) (hσ : σ ^ 2 = 1) (hne : s * x2 + σ * y2 ≠ 0) : False := by
    apply hP.nonsq ((s * x1 + σ * e * y1) / (x1 * y1 * (s * x2 + σ * y2)))
    rw [div_pow, key σ hσ]
    field_simp
  by_cases hp : s * x2 + 1 * y2 = 0
  · by_cases hm : s * x2 + (-1) * y2 = 0
    · apply hy2
      have : (2 : F) * y2 = 0 := by linear_combination hp - hm
      exact (mul_eq_zero.mp this).resolve_left hP.two
    · exact sq (-1) (by ring) hm
  · exact sq 1 (by ring) hp

theorem den_add_ne (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    1 + d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  apply sq_ne_one hP h1 h2
  linear_combination (d * x1 * x2 * y1 * y2 - 1) * h

theorem den_sub_ne (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    1 - d * x1 * x2 * y1 * y2 ≠ 0 := by
  intro h
  apply sq_ne_one hP h1 h2
  linear_combination (-1 - d * x1 * x2 * y1 * y2) * h

theorem onCurve_add (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    OnCurve d (addX d x1 y1 x2 y2) (addY d x1 y1 x2 y2) := by
  have a := den_add_ne hP h1 h2
  have b := den_sub_ne hP h1 h2
  have key : -(x1 * y2 + y1 * x2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
      (y1 * y2 + x1 * x2) ^ 2 * (1 + d * x1 * x2 * y1 * y2) ^ 2 =
      (1 + d * x1 * x2 * y1 * y2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) ^ 2 +
        d * (x1 * y2 + y1 * x2) ^ 2 * (y1 * y2 + x1 * x2) ^ 2 := by
    unfold OnCurve at h1 h2
    linear_combination (d^3*x1^2*x2^4*y1^2*y2^4 - d^2*x1^2*x2^4*y2^4 + d^2*x2^4*y1^2*y2^4 - d^2*x2^4*y2^4 - d*x1^2*x2^4*y2^2 + d*x2^4*y1^2*y2^2 + d*x1^2*x2^2*y2^4 - 2*d*x2^4*y2^4 - d*x2^2*y1^2*y2^4 - 2*x2^4*y2^2 + 2*x2^2*y2^4 - 2*d*x2^2*y2^2 + x2^4 - 4*x2^2*y2^2 + y2^4) * h1 + (d*x1^4*x2^2*y2^2 + d*x2^2*y1^4*y2^2 + 2*d*x1^2*x2^2*y2^2 - 2*d*x2^2*y1^2*y2^2 + 2*x1^2*x2^2*y2^2 - 2*x2^2*y1^2*y2^2 + d*x2^2*y2^2 - x1^2*x2^2 + x2^2*y1^2 + x1^2*y2^2 + 2*x2^2*y2^2 - y1^2*y2^2 - x2^2 + y2^2 + 1) * h2
  unfold OnCurve addX addY
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hu := mul_inv_cancel₀ a
  have hv := mul_inv_cancel₀ b
  set u := (1 + d * x1 * x2 * y1 * y2)⁻¹
  set v := (1 - d * x1 * x2 * y1 * y2)⁻¹
  set X := x1 * y2 + y1 * x2
  set Y := y1 * y2 + x1 * x2
  set D1 := 1 + d * x1 * x2 * y1 * y2
  set D2 := 1 - d * x1 * x2 * y1 * y2
  linear_combination u ^ 2 * v ^ 2 * key + (D1 * D2 ^ 2 * u * v ^ 2 - D1 * Y ^ 2 * u * v ^ 2 +
    D2 ^ 2 * v ^ 2 - Y ^ 2 * v ^ 2) * hu + (D2 * X ^ 2 * u ^ 2 * v + X ^ 2 * u ^ 2 + D2 * v + 1) * hv

end

/-! ## Associativity -/

section
variable (d : F) {X Y δx δy a b : F}

theorem frac_num (hx : δx ≠ 0) (hy : δy ≠ 0) (p q : F) :
    X / δx * p + Y / δy * q = (X * δy * p + Y * δx * q) / (δx * δy) := by
  field_simp

theorem frac_den (hx : δx ≠ 0) (hy : δy ≠ 0) (c : F) :
    1 + c * (X / δx) * (Y / δy) = (δx * δy + c * X * Y) / (δx * δy) := by
  field_simp

theorem addX_div_left (hx : δx ≠ 0) (hy : δy ≠ 0) :
    addX d (X / δx) (Y / δy) a b = (X * δy * b + Y * δx * a) / (δx * δy + d * X * Y * a * b) := by
  have hk : δx * δy ≠ 0 := mul_ne_zero hx hy
  unfold addX
  rw [frac_num hx hy, show 1 + d * (X / δx) * a * (Y / δy) * b = 1 + (d * a * b) * (X / δx) * (Y / δy)
    by ring, frac_den hx hy, div_div_div_cancel_right₀ hk]
  ring_nf

theorem addY_div_left (hx : δx ≠ 0) (hy : δy ≠ 0) :
    addY d (X / δx) (Y / δy) a b = (Y * δx * b + X * δy * a) / (δx * δy - d * X * Y * a * b) := by
  have hk : δx * δy ≠ 0 := mul_ne_zero hx hy
  unfold addY
  rw [show Y / δy * b + X / δx * a = X / δx * a + Y / δy * b by ring, frac_num hx hy,
    show 1 - d * (X / δx) * a * (Y / δy) * b = 1 + (-(d * a * b)) * (X / δx) * (Y / δy) by ring,
    frac_den hx hy, div_div_div_cancel_right₀ hk]
  ring_nf

theorem addX_div_right (hx : δx ≠ 0) (hy : δy ≠ 0) :
    addX d a b (X / δx) (Y / δy) = (a * Y * δx + b * X * δy) / (δx * δy + d * a * X * b * Y) := by
  have hk : δx * δy ≠ 0 := mul_ne_zero hx hy
  unfold addX
  rw [show a * (Y / δy) + b * (X / δx) = X / δx * b + Y / δy * a by ring, frac_num hx hy,
    show 1 + d * a * (X / δx) * b * (Y / δy) = 1 + (d * a * b) * (X / δx) * (Y / δy) by ring,
    frac_den hx hy, div_div_div_cancel_right₀ hk]
  ring_nf

theorem addY_div_right (hx : δx ≠ 0) (hy : δy ≠ 0) :
    addY d a b (X / δx) (Y / δy) = (b * Y * δx + a * X * δy) / (δx * δy - d * a * X * b * Y) := by
  have hk : δx * δy ≠ 0 := mul_ne_zero hx hy
  unfold addY
  rw [show b * (Y / δy) + a * (X / δx) = X / δx * a + Y / δy * b by ring, frac_num hx hy,
    show 1 - d * a * (X / δx) * b * (Y / δy) = 1 + (-(d * a * b)) * (X / δx) * (Y / δy) by ring,
    frac_den hx hy, div_div_div_cancel_right₀ hk]
  ring_nf

end

section
variable {d x1 y1 x2 y2 x3 y3 : F}

theorem add_assoc_x (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2)
    (h3 : OnCurve d x3 y3) :
    addX d (addX d x1 y1 x2 y2) (addY d x1 y1 x2 y2) x3 y3 =
      addX d x1 y1 (addX d x2 y2 x3 y3) (addY d x2 y2 x3 y3) := by
  have a12 := den_add_ne hP h1 h2
  have b12 := den_sub_ne hP h1 h2
  have a23 := den_add_ne hP h2 h3
  have b23 := den_sub_ne hP h2 h3
  have hL := den_add_ne hP (onCurve_add hP h1 h2) h3
  have hR := den_add_ne hP h1 (onCurve_add hP h2 h3)
  rw [show addX d (addX d x1 y1 x2 y2) (addY d x1 y1 x2 y2) x3 y3 = _ from addX_div_left d a12 b12,
    show addX d x1 y1 (addX d x2 y2 x3 y3) (addY d x2 y2 x3 y3) = _ from addX_div_right d a23 b23]
  unfold addX at hL hR
  unfold addY at hL hR
  rw [show 1 + d * ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) * x3 *
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) * y3 = 1 + (d * x3 * y3) *
      ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) *
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) by ring, frac_den a12 b12] at hL
  rw [show 1 + d * x1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) * y1 *
      ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) = 1 + (d * x1 * y1) *
      ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) *
      ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) by ring, frac_den a23 b23] at hR
  have hL' := (div_ne_zero_iff.mp hL).1
  have hR' := (div_ne_zero_iff.mp hR).1
  rw [div_eq_div_iff (by convert hL' using 1; ring) (by convert hR' using 1; ring)]
  unfold OnCurve at h1 h2 h3
  linear_combination (-d^2*x1*x2^4*x3^2*y2^3*y3 + d^2*x2^3*x3^2*y1*y2^4*y3 + d^2*x2^4*x3*y1*y2^3*y3^2 - d^2*x1*x2^3*x3*y2^4*y3^2 - d*x1*x2^3*x3^3*y2^2 - d*x2^2*x3^3*y1*y2^3 - d*x1*x2^4*x3^2*y2*y3 - d*x2*x3^2*y1*y2^4*y3 + d*x2^4*x3*y1*y2*y3^2 + d*x1*x2*x3*y2^4*y3^2 + d*x2^3*y1*y2^2*y3^3 + d*x1*x2^2*y2^3*y3^3 - d*x1*x2^3*x3*y2^2 - d*x2^2*x3*y1*y2^3 - d*x2^3*y1*y2^2*y3 - d*x1*x2^2*y2^3*y3) * h1 + (d^2*x1^2*x2^2*x3^3*y1*y2*y3^2 + d^2*x1*x2*x3^3*y1^2*y2^2*y3^2 - d^2*x1*x2^2*x3^2*y1^2*y2*y3^3 - d^2*x1^2*x2*x3^2*y1*y2^2*y3^3 + d*x1^3*x2^2*x3^2*y2*y3 - d*x1*x2^2*x3^2*y1^2*y2*y3 - d*x1^2*x2*x3^2*y1*y2^2*y3 + d*x2*x3^2*y1^3*y2^2*y3 + d*x1^3*x2*x3^3*y3^2 - d*x1*x2*x3^3*y1^2*y3^2 - d*x1^2*x2^2*x3*y1*y2*y3^2 + d*x1^2*x3^3*y1*y2*y3^2 + d*x2^2*x3*y1^3*y2*y3^2 - d*x3^3*y1^3*y2*y3^2 + d*x1^3*x2*x3*y2^2*y3^2 - d*x1*x2*x3*y1^2*y2^2*y3^2 + d*x1^2*x2*x3^2*y1*y3^3 - d*x2*x3^2*y1^3*y3^3 + d*x1^3*x3^2*y2*y3^3 - d*x1*x3^2*y1^2*y2*y3^3 + d*x1*x2^2*x3^2*y2*y3 - d*x2*x3^2*y1*y2^2*y3 + d*x1*x2*x3^3*y3^2 - d*x2^2*x3*y1*y2*y3^2 + d*x3^3*y1*y2*y3^2 + d*x1*x2*x3*y2^2*y3^2 + d*x2*x3^2*y1*y3^3 + d*x1*x3^2*y2*y3^3 + x1^3*x2*x3^3 - x1*x2*x3^3*y1^2 + x1^2*x3^3*y1*y2 - x3^3*y1^3*y2 + x1^2*x2*x3^2*y1*y3 - x2*x3^2*y1^3*y3 + x1^3*x3^2*y2*y3 - x1*x3^2*y1^2*y2*y3 - x1^3*x2*x3*y3^2 + x1*x2*x3*y1^2*y3^2 - x1^2*x3*y1*y2*y3^2 + x3*y1^3*y2*y3^2 - x1^2*x2*y1*y3^3 + x2*y1^3*y3^3 - x1^3*y2*y3^3 + x1*y1^2*y2*y3^3 + x1^3*x2*x3 + x1*x2*x3^3 - x1*x2*x3*y1^2 + x1^2*x3*y1*y2 + x3^3*y1*y2 - x3*y1^3*y2 + x1^2*x2*y1*y3 + x2*x3^2*y1*y3 - x2*y1^3*y3 + x1^3*y2*y3 + x1*x3^2*y2*y3 - x1*y1^2*y2*y3 - x1*x2*x3*y3^2 - x3*y1*y2*y3^2 - x2*y1*y3^3 - x1*y2*y3^3 + x1*x2*x3 + x3*y1*y2 + x2*y1*y3 + x1*y2*y3) * h2 + (-d*x1^2*x2^2*x3*y1*y2 - d*x1*x2*x3*y1^2*y2^2 + d*x1*x2^2*y1^2*y2*y3 + d*x1^2*x2*y1*y2^2*y3 - x1^3*x2^3*x3 + x1*x2^3*x3*y1^2 - x1^2*x2^2*x3*y1*y2 + x2^2*x3*y1^3*y2 + x1^3*x2*x3*y2^2 - x1*x2*x3*y1^2*y2^2 + x1^2*x3*y1*y2^3 - x3*y1^3*y2^3 - x1^2*x2^3*y1*y3 + x2^3*y1^3*y3 - x1^3*x2^2*y2*y3 + x1*x2^2*y1^2*y2*y3 + x1^2*x2*y1*y2^2*y3 - x2*y1^3*y2^2*y3 + x1^3*y2^3*y3 - x1*y1^2*y2^3*y3 - x1^3*x2*x3 - x1*x2^3*x3 + x1*x2*x3*y1^2 - x1^2*x3*y1*y2 - x2^2*x3*y1*y2 + x3*y1^3*y2 + x1*x2*x3*y2^2 + x3*y1*y2^3 - x1^2*x2*y1*y3 - x2^3*y1*y3 + x2*y1^3*y3 - x1^3*y2*y3 - x1*x2^2*y2*y3 + x1*y1^2*y2*y3 + x2*y1*y2^2*y3 + x1*y2^3*y3 - x1*x2*x3 - x3*y1*y2 - x2*y1*y3 - x1*y2*y3) * h3

theorem add_assoc_y (hP : Params d) (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2)
    (h3 : OnCurve d x3 y3) :
    addY d (addX d x1 y1 x2 y2) (addY d x1 y1 x2 y2) x3 y3 =
      addY d x1 y1 (addX d x2 y2 x3 y3) (addY d x2 y2 x3 y3) := by
  have a12 := den_add_ne hP h1 h2
  have b12 := den_sub_ne hP h1 h2
  have a23 := den_add_ne hP h2 h3
  have b23 := den_sub_ne hP h2 h3
  have hL := den_sub_ne hP (onCurve_add hP h1 h2) h3
  have hR := den_sub_ne hP h1 (onCurve_add hP h2 h3)
  rw [show addY d (addX d x1 y1 x2 y2) (addY d x1 y1 x2 y2) x3 y3 = _ from addY_div_left d a12 b12,
    show addY d x1 y1 (addX d x2 y2 x3 y3) (addY d x2 y2 x3 y3) = _ from addY_div_right d a23 b23]
  unfold addX at hL hR
  unfold addY at hL hR
  rw [show 1 - d * ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) * x3 *
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) * y3 = 1 + (-(d * x3 * y3)) *
      ((x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)) *
      ((y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)) by ring, frac_den a12 b12] at hL
  rw [show 1 - d * x1 * ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) * y1 *
      ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) = 1 + (-(d * x1 * y1)) *
      ((x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)) *
      ((y2 * y3 + x2 * x3) / (1 - d * x2 * x3 * y2 * y3)) by ring, frac_den a23 b23] at hR
  have hL' := (div_ne_zero_iff.mp hL).1
  have hR' := (div_ne_zero_iff.mp hR).1
  rw [div_eq_div_iff (by convert hL' using 1; ring) (by convert hR' using 1; ring)]
  unfold OnCurve at h1 h2 h3
  linear_combination (-d^2*x2^4*x3^2*y1*y2^3*y3 + d^2*x1*x2^3*x3^2*y2^4*y3 + d^2*x1*x2^4*x3*y2^3*y3^2 - d^2*x2^3*x3*y1*y2^4*y3^2 - d*x2^3*x3^3*y1*y2^2 - d*x1*x2^2*x3^3*y2^3 - d*x2^4*x3^2*y1*y2*y3 - d*x1*x2*x3^2*y2^4*y3 + d*x1*x2^4*x3*y2*y3^2 + d*x2*x3*y1*y2^4*y3^2 + d*x1*x2^3*y2^2*y3^3 + d*x2^2*y1*y2^3*y3^3 - d*x2^3*x3*y1*y2^2 - d*x1*x2^2*x3*y2^3 - d*x1*x2^3*y2^2*y3 - d*x2^2*y1*y2^3*y3) * h1 + (-d^2*x1*x2^2*x3^3*y1^2*y2*y3^2 - d^2*x1^2*x2*x3^3*y1*y2^2*y3^2 + d^2*x1^2*x2^2*x3^2*y1*y2*y3^3 + d^2*x1*x2*x3^2*y1^2*y2^2*y3^3 + d*x1^2*x2^2*x3^2*y1*y2*y3 - d*x2^2*x3^2*y1^3*y2*y3 - d*x1^3*x2*x3^2*y2^2*y3 + d*x1*x2*x3^2*y1^2*y2^2*y3 + d*x1^2*x2*x3^3*y1*y3^2 - d*x2*x3^3*y1^3*y3^2 - d*x1^3*x2^2*x3*y2*y3^2 + d*x1^3*x3^3*y2*y3^2 + d*x1*x2^2*x3*y1^2*y2*y3^2 - d*x1*x3^3*y1^2*y2*y3^2 + d*x1^2*x2*x3*y1*y2^2*y3^2 - d*x2*x3*y1^3*y2^2*y3^2 + d*x1^3*x2*x3^2*y3^3 - d*x1*x2*x3^2*y1^2*y3^3 + d*x1^2*x3^2*y1*y2*y3^3 - d*x3^2*y1^3*y2*y3^3 + d*x2^2*x3^2*y1*y2*y3 - d*x1*x2*x3^2*y2^2*y3 + d*x2*x3^3*y1*y3^2 - d*x1*x2^2*x3*y2*y3^2 + d*x1*x3^3*y2*y3^2 + d*x2*x3*y1*y2^2*y3^2 + d*x1*x2*x3^2*y3^3 + d*x3^2*y1*y2*y3^3 + x1^2*x2*x3^3*y1 - x2*x3^3*y1^3 + x1^3*x3^3*y2 - x1*x3^3*y1^2*y2 + x1^3*x2*x3^2*y3 - x1*x2*x3^2*y1^2*y3 + x1^2*x3^2*y1*y2*y3 - x3^2*y1^3*y2*y3 - x1^2*x2*x3*y1*y3^2 + x2*x3*y1^3*y3^2 - x1^3*x3*y2*y3^2 + x1*x3*y1^2*y2*y3^2 - x1^3*x2*y3^3 + x1*x2*y1^2*y3^3 - x1^2*y1*y2*y3^3 + y1^3*y2*y3^3 + x1^2*x2*x3*y1 + x2*x3^3*y1 - x2*x3*y1^3 + x1^3*x3*y2 + x1*x3^3*y2 - x1*x3*y1^2*y2 + x1^3*x2*y3 + x1*x2*x3^2*y3 - x1*x2*y1^2*y3 + x1^2*y1*y2*y3 + x3^2*y1*y2*y3 - y1^3*y2*y3 - x2*x3*y1*y3^2 - x1*x3*y2*y3^2 - x1*x2*y3^3 - y1*y2*y3^3 + x2*x3*y1 + x1*x3*y2 + x1*x2*y3 + y1*y2*y3) * h2 + (d*x1*x2^2*x3*y1^2*y2 + d*x1^2*x2*x3*y1*y2^2 - d*x1^2*x2^2*y1*y2*y3 - d*x1*x2*y1^2*y2^2*y3 - x1^2*x2^3*x3*y1 + x2^3*x3*y1^3 - x1^3*x2^2*x3*y2 + x1*x2^2*x3*y1^2*y2 + x1^2*x2*x3*y1*y2^2 - x2*x3*y1^3*y2^2 + x1^3*x3*y2^3 - x1*x3*y1^2*y2^3 - x1^3*x2^3*y3 + x1*x2^3*y1^2*y3 - x1^2*x2^2*y1*y2*y3 + x2^2*y1^3*y2*y3 + x1^3*x2*y2^2*y3 - x1*x2*y1^2*y2^2*y3 + x1^2*y1*y2^3*y3 - y1^3*y2^3*y3 - x1^2*x2*x3*y1 - x2^3*x3*y1 + x2*x3*y1^3 - x1^3*x3*y2 - x1*x2^2*x3*y2 + x1*x3*y1^2*y2 + x2*x3*y1*y2^2 + x1*x3*y2^3 - x1^3*x2*y3 - x1*x2^3*y3 + x1*x2*y1^2*y3 - x1^2*y1*y2*y3 - x2^2*y1*y2*y3 + y1^3*y2*y3 + x1*x2*y2^2*y3 + y1*y2^3*y3 - x2*x3*y1 - x1*x3*y2 - x1*x2*y3 - y1*y2*y3) * h3

end

end VG.Proof.Ed25519.Edwards
