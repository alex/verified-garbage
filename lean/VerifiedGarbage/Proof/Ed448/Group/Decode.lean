import VerifiedGarbage.Proof.Ed448.Group.Projective

/-!
# Decoded points are on the curve

`recoverX` only returns an `x` with `v x² = u` (or its negation), which is the
curve's equation; so a decoded point, with `Z = 1`, represents a point of the
group (RFC 8032 §5.2.3).
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)
open Edwards

/-- `(d y² - 1) x² = y² - 1` is the curve's equation. -/
theorem onCurve_of_root {x y : Fe}
    (h : (Spec.Ed448.d * y * y - 1) * x * x = y * y - 1) : OnCurve dZ (toZ x) (toZ y) := by
  have e := congrArg toZ h
  simp only [toZ_mul, toZ_sub, toZ_one] at e
  unfold OnCurve dZ
  linear_combination -e

theorem recoverX_root {y x : Fe} {sign : Bool} (h : Spec.Ed448.recoverX y sign = some x) :
    (Spec.Ed448.d * y * y - 1) * x * x = y * y - 1 := by
  unfold Spec.Ed448.recoverX at h
  dsimp only at h
  generalize hc : (y * y - 1) * (y * y - 1) * (y * y - 1) * (Spec.Ed448.d * y * y - 1) *
    Spec.X448.pow ((y * y - 1) * (y * y - 1) * (y * y - 1) * (y * y - 1) * (y * y - 1) *
      (Spec.Ed448.d * y * y - 1) * (Spec.Ed448.d * y * y - 1) * (Spec.Ed448.d * y * y - 1))
      ((P - 3) / 4) = c at h
  have hneg : (Spec.Ed448.d * y * y - 1) * c * c = y * y - 1 →
      (Spec.Ed448.d * y * y - 1) * (0 - c) * (0 - c) = y * y - 1 := by
    intro hw
    apply toZ_inj.mp
    have e := congrArg toZ hw
    simp only [toZ_mul, toZ_sub, toZ_zero] at e ⊢
    linear_combination e
  by_cases h1 : (Spec.Ed448.d * y * y - 1) * c * c ≠ y * y - 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h; cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
  have h1 := not_not.mp h1
  by_cases h2 : (decide (c = 0) && sign) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at h; cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2), Option.some.injEq] at h
  subst h
  by_cases h3 : ((c.val % 2 == 1) == sign) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]; exact h1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]; exact hneg h1

theorem recoverX_on {y x : Fe} {sign : Bool} (h : Spec.Ed448.recoverX y sign = some x) :
    OnCurve dZ (toZ x) (toZ y) :=
  onCurve_of_root (recoverX_root h)

/-- A decoded point is `(x, y, 1)` for the `x` that `recoverX` returns. -/
theorem decodePoint_eq {bs : List Byte} {p : Point} (h : Spec.Ed448.decodePoint bs = some p) :
    ∃ x y sign, Spec.Ed448.recoverX y sign = some x ∧ p = ⟨x, y, 1⟩ := by
  unfold Spec.Ed448.decodePoint at h
  split at h
  · cases h
  · dsimp only [-Nat.reducePow] at h
    split at h
    · rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hr, hp⟩ := h
      cases hp
      exact ⟨x, _, _, hr, rfl⟩
    · cases h

theorem decodePoint_rep {bs : List Byte} {p : Point} (h : Spec.Ed448.decodePoint bs = some p) :
    ∃ a, Rep p a := by
  obtain ⟨x, y, _, hr, rfl⟩ := decodePoint_eq h
  exact ⟨_, rep_affine x y (recoverX_on hr)⟩

theorem decodePoint_valid {bs : List Byte} {p : Point} (h : Spec.Ed448.decodePoint bs = some p) :
    Valid p :=
  (decodePoint_rep h).elim fun _ hr => hr.valid

theorem decodePoint_z {bs : List Byte} {p : Point} (h : Spec.Ed448.decodePoint bs = some p) :
    p.Z = 1 := by
  obtain ⟨x, y, _, _, rfl⟩ := decodePoint_eq h
  rfl

end VG.Proof.Ed448
