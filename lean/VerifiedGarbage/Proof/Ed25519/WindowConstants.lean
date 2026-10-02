import VerifiedGarbage.Impl.Ed25519.BaseMultiples
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.Group.Decode

/-!
# The small multiples of the base point represent `[i + 1]B`

Untrusted. `checkMultiples` walks the list of affine multiples once, adding
the base point with the specification's formula as it goes and comparing
projectively, so the kernel evaluates fourteen additions. The cached
negations are checked entry by entry.
-/

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519 VG.Impl.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- The extended point `(x, y, 1, xy)`. -/
def affPt (q : Fe × Fe) : Point := ⟨q.1, q.2, 1, q.1 * q.2⟩

private def checkMultiples (p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkMultiples (pointAdd (affPt q) basePoint) qs

private theorem checkMultiples_ok (p : Point) (a : EPoint dZ) (h : Rep p a) (qs : List (Fe × Fe))
    (hc : checkMultiples p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • baseAff + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkMultiples, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hrest⟩ := hc
    have hq : Rep (affPt q) a := by
      refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
      · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hx]
      · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hy]
    cases i with
    | zero => simpa using hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq basePoint_rep) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ]
      convert this using 1
      rw [succ_nsmul]; abel

private theorem multiples_check : checkMultiples basePoint baseMultiples = true := by decide +kernel

private theorem multiples_length : baseMultiples.length = 15 := by decide

theorem baseMultiple_rep (i : Nat) (hi : i < 15) :
    Rep (affPt (baseMultiples.getD i (0, 1))) ((i + 1) • baseAff) := by
  have h := checkMultiples_ok basePoint baseAff basePoint_rep baseMultiples
    multiples_check i (multiples_length ▸ hi)
  rwa [succ_nsmul]

private theorem negTable_eq :
    negBaseCachedTable = baseMultiples.map fun m => cache (negPoint (affPt m)) := by decide +kernel

theorem negBaseCached_ok (i : Nat) (hi : i < 15) :
    ∃ q, negBaseCached i = cache q ∧ Rep q ((i + 1) • (-baseAff)) := by
  refine ⟨negPoint (affPt (baseMultiples.getD i (0, 1))), ?_, ?_⟩
  · rw [negBaseCached, negTable_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem (by rw [multiples_length]; omega)]
    rfl
  · rw [smul_neg]; exact (baseMultiple_rep i hi).neg

end VG.Proof.Ed25519
