import VerifiedGarbage.Proof.TripleDes.Permutation

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

def substitutionPrefix (x : BitVec 48) (n : Nat) : BitVec 32 :=
  (List.range n).foldl (fun out i =>
    (out <<< 4) ||| (sBox i ((x >>> (6 * (7 - i))).setWidth 6)).zeroExtend 32) 0

theorem substitutionPrefix_bit (x : BitVec 48) (n : Nat) (hn : n ≤ 8)
    (j : Nat) (hj : j < 32) :
    (substitutionPrefix x n).getLsbD j =
      if j < 4 * n then
        (sBox (n - 1 - j / 4)
          ((x >>> (6 * (7 - (n - 1 - j / 4)))).setWidth 6)).getLsbD (j % 4)
      else false := by
  induction n generalizing j with
  | zero => simp [substitutionPrefix]
  | succ n ih =>
    unfold substitutionPrefix
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    by_cases hlow : j < 4
    · have hdiv : j / 4 = 0 := Nat.div_eq_of_lt hlow
      have hmod : j % 4 = j := Nat.mod_eq_of_lt hlow
      have hbound : j < 4 * (n + 1) := by omega
      simp only [hlow, decide_true, Bool.not_true, Bool.false_and, Bool.false_or,
        hbound, ite_true, hdiv, hmod, Nat.sub_zero, Nat.add_sub_cancel]
    · have hj' : j - 4 < 32 := by omega
      have ih' := ih (by omega) (j - 4) hj'
      change ((!decide (j < 4) &&
        (substitutionPrefix x n).getLsbD (j - 4)) ||
        (sBox n ((x >>> (6 * (7 - n))).setWidth 6)).getLsbD j) = _
      rw [BitVec.getLsbD_of_ge (sBox n ((x >>> (6 * (7 - n))).setWidth 6)) j (by omega), ih']
      simp only [hlow, decide_false, Bool.not_false, Bool.true_and, Bool.or_false]
      have hdiv : (j - 4) / 4 = j / 4 - 1 := by omega
      have hmod : (j - 4) % 4 = j % 4 := by omega
      have hidx : n - 1 - (j - 4) / 4 = n + 1 - 1 - j / 4 := by omega
      have hbound : (j - 4 < 4 * n) ↔ (j < 4 * (n + 1)) := by omega
      simp only [hbound, hidx, hmod]

theorem roundFunction_bit (r : BitVec 32) (k : BitVec 48) (j : Nat) (hj : j < 32) :
    (roundFunction r k).getLsbD j =
      let t := 32 - p.getD (31 - j) 1
      (sBox (7 - t / 4)
        (((permute expansion r ^^^ k) >>> (6 * (7 - (7 - t / 4)))).setWidth 6)).getLsbD
        (t % 4) := by
  have bounds : ∀ j < 32, 1 ≤ p.getD j 1 ∧ p.getD j 1 ≤ 32 := by decide +kernel
  obtain ⟨lo, hi⟩ := bounds (31 - j) (by omega)
  have ht : 32 - p.getD (31 - j) 1 < 32 := by omega
  unfold roundFunction
  rw [permute_bit _ _ (by decide) j hj]
  change (substitutionPrefix (permute expansion r ^^^ k) 8).getLsbD
    (32 - p.getD (32 - 1 - j) 1) = _
  rw [substitutionPrefix_bit _ 8 (by decide) _ ht]
  simp only [ht, ite_true]

end VG.Proof.TripleDes
