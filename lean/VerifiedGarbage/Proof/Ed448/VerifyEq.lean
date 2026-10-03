import VerifiedGarbage.Proof.Ed448.Group.Decode
import Mathlib.Tactic.Abel

/-!
# Ed448: the verification equation, as code checks it

`verifyEquation` (RFC 8032 §5.2.7, cofactored) in terms of what code
computes: for decoded `A` and `R`, `[4]([S]B + [k](-A))` against `[4]R`,
each doubled twice from representatives `Q` and `R`. Over the group
`[4]([S]B - [k]A) = [4]R` exactly when `[4][S]B = [4]R + [4][k]A`.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)
open Edwards

theorem verifyEquation_none {pk sig ch : List Byte}
    (h : Spec.Ed448.decodePoint pk = none ∨ Spec.Ed448.decodePoint (sig.take 57) = none) :
    Spec.Ed448.verifyEquation pk sig ch = false := by
  unfold Spec.Ed448.verifyEquation
  split
  · rfl
  · rcases h with h | h
    · simp only [h]
    · rw [h]; cases Spec.Ed448.decodePoint pk <;> rfl

theorem four_smul {a : EPoint dZ} : (a + a) + (a + a) = 4 • a := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, add_nsmul, add_nsmul, add_nsmul, one_nsmul]
  abel

theorem verifyEquation_some {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114)
    (hc : ch.length = 57) {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a)
    (hr : Spec.Ed448.decodePoint (sig.take 57) = some r) {Q R : Point}
    (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-toAffine a))) (hR : Rep R (toAffine r)) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (double (double Q)) (double (double R))) := by
  have hva := decodePoint_valid ha
  have hvr := decodePoint_valid hr
  unfold Spec.Ed448.verifyEquation
  simp only [hl, hs, hc, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false, ha, hr]
  congr 1
  generalize Spec.Ed448.decodeLE (sig.drop 57) = S at *
  generalize Spec.Ed448.decodeLE ch = K at *
  have h1 := pointMul_rep 4 (pointMul_rep S basePoint_rep)
  have h2 := pointAdd_rep (pointMul_rep 4 (rep_toAffine hvr)) (pointMul_rep 4 (pointMul_rep K (rep_toAffine hva)))
  have h3 := double_rep (double_rep hQ)
  have h4 := double_rep (double_rep hR)
  rw [Bool.eq_iff_iff, pointEqual_rep h1 h2, pointEqual_rep h3 h4, four_smul, four_smul]
  constructor
  · intro h
    rw [smul_add, smul_neg, h]; abel
  · intro h
    have : 4 • (S • baseAff) = 4 • (S • baseAff + K • -toAffine a) + 4 • (K • toAffine a) := by
      rw [smul_add (4 : Nat) (S • baseAff), smul_neg]; abel
    rw [this, h]

end VG.Proof.Ed448
