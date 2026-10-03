import VerifiedGarbage.Proof.Weierstrass.Affine
import VerifiedGarbage.Proof.Weierstrass.Field

/-!
# The complete formulas compute the specification's group law

`Rep C X Y Z P`: the projective triple `(X : Y : Z)` over `ZMod C.p`
represents the point `P` of the specification (`O` is `(0 : Y : 0)` with
`Y ≠ 0`, `(x, y)` is `(xZ : yZ : Z)` with `Z ≠ 0`). On a curve with no point
of order 2 (`Good`), `rcbAdd` maps representatives of two points of the
curve to a representative of their sum by the specification's `add`
(`rcbAdd_rep`), whichever case of SEC 1's group law applies: the formulas
are complete. The sum of two points of the curve is on the curve
(`onCurve_add`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- `(X : Y : Z)` represents `P`. -/
def Rep (C : Curve) (X Y Z : ZMod C.p) : Point C → Prop
  | .infinity => X = 0 ∧ Y ≠ 0 ∧ Z = 0
  | .affine x y => Z ≠ 0 ∧ X = toF x * Z ∧ Y = toF y * Z

/-- What the proofs need of a curve: a prime field of characteristic above 3,
and no point of order 2 (`x³ + a x + b` has no root). -/
structure Good (C : Curve) : Prop where
  prime : C.p.Prime
  gt3 : 3 < C.p
  noTwoTorsion : ∀ x : ZMod C.p, x ^ 3 + (C.a : ZMod C.p) * x + (C.b : ZMod C.p) ≠ 0

variable {C : Curve}

theorem Good.two_lt (hC : Good C) : 2 < C.p := by have := hC.gt3; omega

theorem onCurve_affine {x y : Fe C} : onCurve C (.affine x y) = true ↔
    toF y ^ 2 = toF x ^ 3 + (C.a : ZMod C.p) * toF x + (C.b : ZMod C.p) := by
  simp only [onCurve, decide_eq_true_eq]
  rw [← toF_inj]
  simp only [toF_add, toF_mul, toF_ofNat]
  constructor <;> intro h <;> linear_combination h

/-! ## The cases of the group law -/

theorem add_affine (x₁ y₁ x₂ y₂ : Fe C) : add (.affine x₁ y₁) (.affine x₂ y₂) =
    if x₁ = x₂ ∧ y₂ = -y₁ then .infinity
    else if x₁ ≠ x₂ then
      let l := (y₂ - y₁) * inv (x₂ - x₁)
      let x₃ := l * l - x₁ - x₂
      .affine x₃ (l * (x₁ - x₃) - y₁)
    else
      let l := (3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)
      let x₃ := l * l - 2 * x₁
      .affine x₃ (l * (x₁ - x₃) - y₁) := rfl

theorem add_neg {x₁ y₁ : Fe C} : add (.affine x₁ y₁) (.affine x₁ (-y₁)) = .infinity := by
  rw [add_affine, ite_eq_left ⟨rfl, rfl⟩]

theorem add_chord {x₁ y₁ x₂ y₂ : Fe C} (hx : x₁ ≠ x₂) : add (.affine x₁ y₁) (.affine x₂ y₂) =
    .affine ((y₂ - y₁) * inv (x₂ - x₁) * ((y₂ - y₁) * inv (x₂ - x₁)) - x₁ - x₂)
      ((y₂ - y₁) * inv (x₂ - x₁) *
        (x₁ - ((y₂ - y₁) * inv (x₂ - x₁) * ((y₂ - y₁) * inv (x₂ - x₁)) - x₁ - x₂)) - y₁) := by
  rw [add_affine, ite_eq_right (fun h => hx h.1), ite_eq_left hx]

theorem add_tangent {x₁ y₁ : Fe C} (hy : y₁ ≠ -y₁) : add (.affine x₁ y₁) (.affine x₁ y₁) =
    .affine ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
        ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) - 2 * x₁)
      ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
        (x₁ - ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁) *
          ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) - 2 * x₁)) - y₁) := by
  rw [add_affine, ite_eq_right (fun h => hy h.2), ite_eq_right (fun h => h rfl)]

section
variable [Fact C.p.Prime]

theorem two_ne_zero' (hp : 2 < C.p) : (2 : ZMod C.p) ≠ 0 := by
  intro h
  have : ((2 : Nat) : ZMod C.p) = ((0 : Nat) : ZMod C.p) := by rw [Nat.cast_ofNat, h, Nat.cast_zero]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp, Nat.zero_mod] at this
  exact absurd this (by decide)

/-- On the curve, points with the same `x` have `y₂ = ±y₁`. -/
theorem y_eq_or_eq_neg {x y₁ y₂ : Fe C} (h1 : onCurve C (.affine x y₁) = true)
    (h2 : onCurve C (.affine x y₂) = true) : y₂ = y₁ ∨ y₂ = -y₁ := by
  rw [onCurve_affine] at h1 h2
  have : (toF y₂ - toF y₁) * (toF y₂ + toF y₁) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp this with h | h
  · exact .inl (toF_injective (sub_eq_zero.mp h))
  · exact .inr (toF_injective (by rw [toF_neg]; linear_combination h))

/-- The slope of the chord, in `ZMod C.p`. -/
theorem toF_chord_slope (hp : 2 < C.p) {x₁ y₁ x₂ y₂ : Fe C} (hx : x₁ ≠ x₂) :
    toF ((y₂ - y₁) * inv (x₂ - x₁)) * (toF x₂ - toF x₁) = toF y₂ - toF y₁ := by
  have hd : toF x₂ - toF x₁ ≠ 0 := fun h => hx (toF_injective (sub_eq_zero.mp h)).symm
  rw [toF_mul, toF_inv hp, toF_sub, toF_sub, inv_mul_cancel_right₀ hd]

/-- The slope of the tangent, in `ZMod C.p`. -/
theorem toF_tangent_slope (hp : 2 < C.p) {x₁ y₁ : Fe C} (hy : 2 * toF y₁ ≠ 0) :
    toF ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) * (2 * toF y₁) =
      3 * toF x₁ ^ 2 + (C.a : ZMod C.p) := by
  rw [toF_mul, toF_inv hp, toF_mul, toF_ofNat' 2, inv_mul_cancel_right₀ hy, toF_add, toF_mul,
    toF_mul, toF_ofNat' 3, toF_ofNat, sq, mul_assoc]

theorem two_mul_ne_zero {y₁ : Fe C} (hy : y₁ ≠ -y₁) : 2 * toF y₁ ≠ 0 := by
  intro h
  apply hy
  apply toF_injective
  rw [toF_neg]
  linear_combination h

/-- The sum of two points of the curve is on the curve. -/
theorem onCurve_add (hp : 2 < C.p) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : onCurve C (add P Q) = true := by
  match P, Q with
  | .infinity, _ => exact hQ
  | .affine _ _, .infinity => exact hP
  | .affine x₁ y₁, .affine x₂ y₂ =>
    by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
    · obtain ⟨rfl, rfl⟩ := hc
      rw [add_neg]; rfl
    by_cases hx : x₁ = x₂
    · subst hx
      obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg hP hQ).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
      have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
      rw [add_tangent hy, onCurve_affine]
      rw [onCurve_affine] at hP
      have := tangent_on hP (two_mul_ne_zero hy) (toF_tangent_slope hp (two_mul_ne_zero hy))
      simp only [toF_sub, toF_mul, toF_ofNat' 2] at this ⊢
      exact this
    · rw [add_chord hx, onCurve_affine]
      rw [onCurve_affine] at hP hQ
      have := chord_on hP hQ (fun h => hx (toF_injective h)) (toF_chord_slope hp hx)
      simp only [toF_sub, toF_mul] at this ⊢
      exact this

/-! ## Representatives -/

theorem Rep.smul {X Y Z c : ZMod C.p} {P : Point C} (hc : c ≠ 0) (h : Rep C X Y Z P) :
    Rep C (c * X) (c * Y) (c * Z) P := by
  cases P with
  | infinity =>
    obtain ⟨hX, hY, hZ⟩ := h
    exact ⟨by rw [hX, mul_zero], mul_ne_zero hc hY, by rw [hZ, mul_zero]⟩
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    exact ⟨mul_ne_zero hc hZ, by rw [hX]; ring, by rw [hY]; ring⟩

/-- On a curve with no point of order 2, `Y ≠ 0`. -/
theorem Rep.y_ne_zero (hC : Good C) {X Y Z : ZMod C.p} {P : Point C}
    (hP : onCurve C P = true) (h : Rep C X Y Z P) : Y ≠ 0 := by
  cases P with
  | infinity => exact h.2.1
  | affine x y =>
    obtain ⟨hZ, -, hY⟩ := h
    rw [hY]
    exact mul_ne_zero (Weierstrass.y_ne_zero hC.noTwoTorsion (onCurve_affine.mp hP)) hZ

theorem rep_infinity : Rep C 0 1 0 .infinity := ⟨rfl, one_ne_zero, rfl⟩

theorem rep_affine (x y : Fe C) : Rep C (toF x) (toF y) 1 (.affine x y) :=
  ⟨one_ne_zero, (mul_one _).symm, (mul_one _).symm⟩

theorem Rep.z_eq_zero_iff {X Y Z : ZMod C.p} {P : Point C} (h : Rep C X Y Z P) :
    Z = 0 ↔ P = .infinity := by
  cases P with
  | infinity => exact ⟨fun _ => rfl, fun _ => h.2.2⟩
  | affine x y => exact ⟨fun h0 => absurd h0 h.1, fun h' => nomatch h'⟩

theorem mul_pow_sub_two {Z : ZMod C.p} (hZ : Z ≠ 0) : Z * Z ^ (C.p - 2) = 1 := by
  have h2 := (Fact.out : C.p.Prime).two_le
  rw [← pow_succ', show C.p - 2 + 1 = C.p - 1 by omega, ZMod.pow_card_sub_one_eq_one hZ]

/-- The affine `x` of a representative: `X / Z`, with the inverse by Fermat. -/
theorem Rep.x_eq {X Y Z : ZMod C.p} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    toF x = X * Z ^ (C.p - 2) := by
  obtain ⟨hZ, hX, -⟩ := h
  rw [hX, mul_assoc, mul_pow_sub_two hZ, mul_one]

theorem Rep.y_eq {X Y Z : ZMod C.p} {x y : Fe C} (h : Rep C X Y Z (.affine x y)) :
    toF y = Y * Z ^ (C.p - 2) := by
  obtain ⟨hZ, -, hY⟩ := h
  rw [hY, mul_assoc, mul_pow_sub_two hZ, mul_one]

theorem Rep.infinity_x {X Y Z : ZMod C.p} (h : Rep C X Y Z .infinity) : X * Z ^ (C.p - 2) = 0 := by
  rw [h.1, zero_mul]

end

/-! ## Completeness -/

theorem Good.onCurve_add (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : onCurve C (add P Q) = true := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  exact Weierstrass.onCurve_add hC.two_lt hP hQ

/-- For points with `Z = 1`. -/
theorem rcbAdd_rep_one (hC : Good C) {x₁ y₁ x₂ y₂ : Fe C} (h1 : onCurve C (.affine x₁ y₁) = true)
    (h2 : onCurve C (.affine x₂ y₂) = true) :
    Rep C (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).1
      (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).2.1
      (rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) (toF x₁) (toF y₁) 1 (toF x₂) (toF y₂) 1).2.2
      (add (.affine x₁ y₁) (.affine x₂ y₂)) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  have hp := hC.two_lt
  have ht := hC.noTwoTorsion
  by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
  · obtain ⟨rfl, rfl⟩ := hc
    rw [add_neg, toF_neg]
    exact rcbAdd_neg ht (two_ne_zero' hp) (onCurve_affine.mp h1)
  by_cases hx : x₁ = x₂
  · subst hx
    obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg h1 h2).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
    have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
    rw [add_tangent hy]
    obtain ⟨hz, hX, hY⟩ := rcbAdd_tangent ht (two_ne_zero' hp) (onCurve_affine.mp h1)
      (toF_tangent_slope hp (two_mul_ne_zero hy))
    refine ⟨hz, ?_, ?_⟩
    · rw [hX]; simp only [toF_sub, toF_mul, toF_ofNat' 2]
    · rw [hY]; simp only [toF_sub, toF_mul, toF_ofNat' 2]
  · rw [add_chord hx]
    obtain ⟨hz, hX, hY⟩ := rcbAdd_chord ht (onCurve_affine.mp h1) (onCurve_affine.mp h2)
      (fun h => hx (toF_injective h)) (toF_chord_slope hp hx)
    refine ⟨hz, ?_, ?_⟩
    · rw [hX]; simp only [toF_sub, toF_mul]
    · rw [hY]; simp only [toF_sub, toF_mul]

/-- **Completeness**: on a curve with no point of order 2, `rcbAdd` maps
representatives of two points of the curve to a representative of their
sum. -/
theorem rcbAdd_rep (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) {X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 : ZMod C.p}
    (h1 : Rep C X1 Y1 Z1 P) (h2 : Rep C X2 Y2 Z2 Q)
    (h : rcbAdd (C.a : ZMod C.p) (3 * (C.b : ZMod C.p)) X1 Y1 Z1 X2 Y2 Z2 = (X3, Y3, Z3)) :
    Rep C X3 Y3 Z3 (add P Q) := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  match P, Q with
  | .infinity, Q =>
    obtain ⟨rfl, hY1, rfl⟩ := h1
    rw [rcbAdd_zero_left, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact h2.smul (mul_ne_zero (pow_ne_zero 2 hY1) (h2.y_ne_zero hC hQ))
  | .affine x y, .infinity =>
    obtain ⟨rfl, hY2, rfl⟩ := h2
    rw [rcbAdd_comm, rcbAdd_zero_left, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact h1.smul (mul_ne_zero (pow_ne_zero 2 hY2) (h1.y_ne_zero hC hP))
  | .affine x₁ y₁, .affine x₂ y₂ =>
    obtain ⟨hZ1, rfl, rfl⟩ := h1
    obtain ⟨hZ2, rfl, rfl⟩ := h2
    rw [rcbAdd_scale, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (rcbAdd_rep_one hC hP hQ).smul
      (mul_ne_zero (pow_ne_zero 2 hZ1) (pow_ne_zero 2 hZ2))

end VG.Proof.Weierstrass
