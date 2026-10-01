import VerifiedGarbage.Proof.Ed25519.Group.Extended

/-!
# Decoded points are on the curve

Untrusted. `recoverX` only returns an `x` with `v x² = u`, which is the
curve's equation; so a decoded point represents a point of the group.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe P)
open Spec.Ed25519 (Point)
open Edwards

theorem recoverX_on {y x : Fe} {sign : Bool} (h : Spec.Ed25519.recoverX y sign = some x) :
    OnCurve dZ (toZ x) (toZ y) := by
  unfold Spec.Ed25519.recoverX at h
  simp only [Option.bind_eq_bind] at h
  set u := y * y - 1
  set v := Spec.Ed25519.d * y * y + 1
  set c := u * Spec.X25519.pow v 3 * Spec.X25519.pow (u * Spec.X25519.pow v 7) ((P - 5) / 8)
  have hcurve : ∀ w : Fe, v * w * w = u → OnCurve dZ (toZ w) (toZ y) := by
    intro w hw
    have e := congrArg toZ hw
    simp only [toZ_mul, toZ_add, toZ_sub, toZ_one, v, u] at e
    unfold OnCurve dZ
    linear_combination -e
  have hneg : ∀ w : Fe, v * w * w = u → v * (0 - w) * (0 - w) = u := by
    intro w hw
    apply toZ_inj.mp
    have e := congrArg toZ hw
    simp only [toZ_mul, toZ_sub, toZ_zero] at e ⊢
    linear_combination e
  have hroot : ∀ w : Fe, (if v * c * c = u then some c else if v * c * c = 0 - u then
      some (c * Spec.Ed25519.sqrtM1) else none) = some w → v * w * w = u := by
    intro w hw
    split_ifs at hw with h1 h2
    · cases hw; exact h1
    · cases hw
      apply toZ_inj.mp
      have e := congrArg toZ h2
      have s := congrArg toZ sqrtM1_sq
      simp only [toZ_mul, toZ_sub, toZ_zero, toZ_one] at e s ⊢
      linear_combination (toZ c * toZ c * toZ v) * s - e
  have fin : ∀ w : Fe, v * w * w = u →
      (if (decide (w = 0) && sign) = true then none
        else some (if ((w.val % 2 == 1) == sign) = true then w else 0 - w)) = some x →
      OnCurve dZ (toZ x) (toZ y) := by
    intro w hw hx
    split_ifs at hx with h3 h4
    · rw [Option.some.injEq] at hx; rw [← hx]; exact hcurve w hw
    · rw [Option.some.injEq] at hx; rw [← hx]; exact hcurve _ (hneg w hw)
  by_cases h1 : v * c * c = u
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), Option.bind_some] at h
    exact fin c h1 h
  · by_cases h2 : v * c * c = 0 - u
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), Option.bind_some] at h
      exact fin _ (hroot _ (by rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
        ite_eq_left_of_eq_true _ _ (eq_true h2)])) h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
        Option.bind_none] at h
      cases h

theorem decodePoint_rep {bs : List Byte} {p : Point} (h : Spec.Ed25519.decodePoint bs = some p) :
    ∃ a, Rep p a := by
  unfold Spec.Ed25519.decodePoint at h
  by_cases h1 : (bs.length != 32) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at h; cases h
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
  by_cases h2 : Spec.Ed25519.decodeLE bs % 2 ^ 255 < P
  · rw [dite_eq_left_of_eq_true (eq_true h2), Option.bind_eq_bind] at h
    dsimp only at h
    cases hr : Spec.Ed25519.recoverX ⟨Spec.Ed25519.decodeLE bs % 2 ^ 255, h2⟩
        (Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1) with
    | none => rw [hr, Option.bind_none] at h; cases h
    | some x =>
      rw [hr, Option.bind_some] at h
      cases h
      exact ⟨_, rep_affine _ _ (recoverX_on hr)⟩
  · rw [dite_eq_right_of_eq_false (eq_false h2)] at h; cases h

end VG.Proof.Ed25519
