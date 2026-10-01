import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-! Fixed permutations in the FIPS numbering convention. Untrusted. -/

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

private theorem prefix_bit {n m : Nat} (positions : Vector Nat m) (x : BitVec n)
    (hn : 0 < n) (k : Nat) (hk : k ≤ m) (j : Nat) (hj : j < m) :
    ((List.range k).foldl (fun (out : BitVec m) i =>
      (out <<< 1) ||| (((x >>> (n - positions.getD i 1)) &&& 1).setWidth m))
      (0 : BitVec m)).getLsbD j =
      if j < k then x.getLsbD (n - positions.getD (k - 1 - j) 1) else false := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
    by_cases hzero : j = 0
    · subst j
      simp [hn]
    · have hj1 : j - 1 < m := by omega
      rw [ih (by omega) (j - 1) hj1]
      have hge : ¬j < 1 := by omega
      have hone : (1 : BitVec n).getLsbD j = false := by
        change (BitVec.ofNat n 1).getLsbD j = false
        rw [BitVec.getLsbD_ofNat]
        have hnat : Nat.testBit 1 j = false := by
          change Nat.testBit (2 ^ 0) j = false
          rw [Nat.testBit_two_pow]
          exact decide_eq_false (Ne.symm hzero)
        rw [hnat, Bool.and_false]
      simp only [hone, Bool.and_false, Bool.or_false, hge,
        decide_false, Bool.not_false, Bool.true_and]
      by_cases hlt : j < k + 1
      · have hlt' : j - 1 < k := by omega
        simp only [hlt, hlt', ite_true]
        have heq : k - 1 - (j - 1) = k + 1 - 1 - j := by omega
        rw [heq]
      · have hlt' : ¬j - 1 < k := by omega
        simp only [hlt, hlt', ite_false]

theorem permute_bit {n m : Nat} (positions : Vector Nat m) (x : BitVec n)
    (hn : 0 < n) (j : Nat) (hj : j < m) :
    (permute positions x).getLsbD j = x.getLsbD (n - positions.getD (m - 1 - j) 1) := by
  have h := prefix_bit positions x hn m (Nat.le_refl m) j hj
  simpa only [permute, hj, ite_true] using h

end VG.Proof.TripleDes
