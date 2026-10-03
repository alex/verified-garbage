import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.DecodeBytes

/-!
# Ed448: recovering `x`, as code computes it

`recoverX` (RFC 8032 §5.2.3) with its products associated as the x86-64
code computes them: `v = d y² - 1`, `u⁵v³ = (u³v)(uv)²`, the power by
`rootPow`'s addition chain, the check `v x² = u`, and `-x = (x - x) - x`.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)

theorem recoverX_eq (y : Fe) (sign : Bool) :
    Spec.Ed448.recoverX y sign =
      let u := y * y - 1
      let v := Spec.Ed448.d * (y * y) - 1
      let t := u * u * u * v
      let x := t * rootPow (t * ((u * v) * (u * v)))
      if v * (x * x) ≠ u then none
      else if x = 0 && sign then none
      else some (if (x.val % 2 == 1) == sign then x else (x - x) - x) := by
  have e1 : Spec.Ed448.d * y * y = Spec.Ed448.d * (y * y) :=
    toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e2 (u v : Fe) : u * u * u * u * u * v * v * v = u * u * u * v * ((u * v) * (u * v)) :=
    toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e3 (v x : Fe) : v * x * x = v * (x * x) := toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e4 (x : Fe) : 0 - x = (x - x) - x := toZ_inj.mp (by simp only [toZ_sub, toZ_zero]; ring)
  unfold Spec.Ed448.recoverX
  dsimp only
  rw [e1]
  generalize y * y - 1 = u
  generalize Spec.Ed448.d * (y * y) - 1 = v
  rw [e2 u v, ← rootPow_eq]
  generalize u * u * u * v * rootPow (u * u * u * v * (u * v * (u * v))) = x
  rw [e3 v x, e4 x]

/-- `decodePoint` of 57 bytes, as the code computes it: from the number `y₀`
of the first 56 bytes and the last byte `b`, `x` as `recoverX_eq` has it, and
the three checks. -/
theorem decodePoint_impl (bs : List Byte) (h : bs.length = 57) (y0 b : Nat)
    (hy0 : Spec.Ed448.decodeLE (bs.take 56) = y0) (hb : (bs.getD 56 0).toNat = b) (Y u v t x : Fe)
    (hY : VG.Proof.X448.toFe y0 = Y) (hu : Y * Y - 1 = u) (hv : Spec.Ed448.d * (Y * Y) - 1 = v)
    (ht : u * u * u * v = t) (hx : t * rootPow (t * ((u * v) * (u * v))) = x) :
    Spec.Ed448.decodePoint bs =
      if (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1) then
        some ⟨if (x.val % 2 == 1) == (b / 128 == 1) then x else (x - x) - x, Y, 1⟩
      else none := by
  rw [decodePoint_bytes bs h, hy0, hb, hY, recoverX_eq]
  dsimp only
  rw [hu, hv, ht, hx]
  have hbool : (decide (x = 0) && (b / 128 == 1)) = true ↔ x = 0 ∧ b / 128 = 1 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hc (h1 : b % 128 = 0 ∧ y0 < P) (h2 : v * (x * x) = u) (h3 : ¬ (x = 0 ∧ b / 128 = 1)) :
      (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1) := ⟨h1, h2, h3⟩
  by_cases h1 : b % 128 = 0 ∧ y0 < P
  · rw [ite_eq_left (c := b % 128 = 0 ∧ y0 < P) h1]
    by_cases h2 : v * (x * x) = u
    · rw [ite_eq_right (c := v * (x * x) ≠ u) (not_not_intro h2)]
      by_cases h3 : x = 0 ∧ b / 128 = 1
      · rw [ite_eq_left (c := (decide (x = 0) && (b / 128 == 1)) = true) (hbool.mpr h3),
          ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
            (fun h => h.2.2 h3)]
        rfl
      · rw [ite_eq_right (c := (decide (x = 0) && (b / 128 == 1)) = true) (fun h => h3 (hbool.mp h)),
          ite_eq_left (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
            (hc h1 h2 h3)]
        rfl
    · rw [ite_eq_left (c := v * (x * x) ≠ u) h2,
        ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
          (fun h => h2 h.2.1)]
      rfl
  · rw [ite_eq_right (c := b % 128 = 0 ∧ y0 < P) h1,
      ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
        (fun h => h1 h.1)]

end VG.Proof.Ed448
