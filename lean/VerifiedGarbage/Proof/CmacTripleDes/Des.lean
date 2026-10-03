import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Impl.CmacTripleDes.Index

/-!
# DES: the bits of the specification's permutations and round function

The specification builds `permute` and the S-boxes' outputs one bit (or
four) at a time, most significant first. These lemmas say which input bit
each output bit is, so that the implementations, checked bit by bit, can be
compared with them.
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes

/-! ## Permutations -/

theorem getLsbD_one' {n j : Nat} : (1 : BitVec n).getLsbD j = (decide (0 < n) && decide (j = 0)) :=
  BitVec.getLsbD_one

theorem getLsbD_permute_prefix {n m : Nat} (pos : Vector Nat m) (x : BitVec n) (hn : 0 < n)
    (k : Nat) (j : Nat) (hj : j < m) :
    ((List.range k).foldl (fun (out : BitVec m) i =>
      (out <<< 1) ||| (((x >>> (n - pos.getD i 1)) &&& 1).setWidth m)) 0).getLsbD j =
      (decide (j < k) && x.getLsbD (n - pos.getD (k - 1 - j) 1)) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, getLsbD_one']
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hn, hj]
    · rw [ih (j - 1) (by omega)]
      simp only [hj, decide_true, Bool.true_and, show ¬ j < 1 by omega, decide_false,
        Bool.not_false, show j ≠ 0 by omega, Bool.and_false, Bool.or_false]
      by_cases hk : j < k + 1
      · rw [show k + 1 - 1 - j = k - 1 - (j - 1) by omega]
        simp [hk, show j - 1 < k by omega]
      · simp [hk, show ¬ j - 1 < k by omega]

/-- Bit `j` of `permute pos x` is bit `n − pos[m − 1 − j]` of `x`. -/
theorem getLsbD_permute {n m : Nat} (pos : Vector Nat m) (x : BitVec n) (hn : 0 < n)
    {j : Nat} (hj : j < m) :
    (permute pos x).getLsbD j = x.getLsbD (n - pos.getD (m - 1 - j) 1) := by
  have h := getLsbD_permute_prefix pos x hn m j hj
  simp only [hj, decide_true, Bool.true_and] at h
  exact h

/-! ## The round function -/

theorem getLsbD_concat4_prefix (g : Nat → BitVec 4) (k q : Nat) (hq : q < 32) :
    ((List.range k).foldl (fun (out : BitVec 32) i => (out <<< 4) ||| (g i).zeroExtend 32) 0).getLsbD q =
      (decide (q < 4 * k) && (g (k - 1 - q / 4)).getLsbD (q % 4)) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h4 : q < 4
    · simp [hq, h4, show q < 4 * (k + 1) by omega, Nat.div_eq_of_lt h4, Nat.mod_eq_of_lt h4]
    · rw [ih (q - 4) (by omega)]
      have e1 : (q - 4) / 4 = q / 4 - 1 := by omega
      have e2 : (q - 4) % 4 = q % 4 := by omega
      simp only [hq, decide_true, Bool.true_and, h4, decide_false, Bool.not_false, e1, e2,
        BitVec.getLsbD_of_ge (g k) q (by omega), Bool.and_false, Bool.or_false]
      by_cases hk : q < 4 * (k + 1)
      · simp [hk, show q - 4 < 4 * k by omega, show k - 1 - (q / 4 - 1) = k + 1 - 1 - q / 4 by omega]
      · simp [hk, show ¬ q - 4 < 4 * k by omega]

/-- Box `i`'s input in the round with input `r` and round key `k`. -/
def chunk (r : BitVec 32) (k : BitVec 48) (i : Nat) : BitVec 6 :=
  ((permute expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem getLsbD_chunk (r : BitVec 32) (k : BitVec 48) {i t : Nat} (hi : i < 8) (ht : t < 6) :
    (chunk r k i).getLsbD t =
      (r.getLsbD (Impl.CmacTripleDes.expSrc (6 * (7 - i) + t)) ^^ k.getLsbD (6 * (7 - i) + t)) := by
  simp only [chunk, BitVec.getLsbD_setWidth, ht, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [getLsbD_permute _ _ (by decide) (by omega)]
  rfl

/-- Bit `j` of `f(r, k)` is output bit `u % 4` of box `7 − u / 4`, where
`u = pSrc j`. -/
theorem getLsbD_roundFunction (r : BitVec 32) (k : BitVec 48) {j : Nat} (hj : j < 32) :
    (roundFunction r k).getLsbD j =
      let u := Impl.CmacTripleDes.pSrc j
      (sBox (7 - u / 4) (chunk r k (7 - u / 4))).getLsbD (u % 4) := by
  have hu : Impl.CmacTripleDes.pSrc j < 32 := by
    revert j; decide
  simp only [roundFunction]
  rw [getLsbD_permute _ _ (by decide) hj, getLsbD_concat4_prefix _ 8 _ (by exact hu)]
  simp only [show 32 - p.getD (32 - 1 - j) 1 = Impl.CmacTripleDes.pSrc j from rfl,
    show Impl.CmacTripleDes.pSrc j < 4 * 8 from hu, decide_true, Bool.true_and,
    show 8 - 1 - Impl.CmacTripleDes.pSrc j / 4 = 7 - Impl.CmacTripleDes.pSrc j / 4 by omega]
  rfl

end VG.Proof.CmacTripleDes
