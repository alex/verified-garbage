import VerifiedGarbage.Spec.Argon2

/-!
# Argon2 H′: lengths and the streaming BLAKE2b specification

The length lemmas describe H′'s 32-byte prefixes and final 33–64-byte
hash. `H_stream` connects the RFC definition to the existing streaming
contract without selecting a BLAKE2b implementation.
-/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem wordList_length (xs : List (BitVec 64)) :
    (xs.flatMap Spec.Blake2.wordBytes).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, Spec.Blake2.wordBytes,
      List.length_map, List.length_range, List.length_cons] at *
    omega

theorem H_length (n : Nat) (input : List Byte) (hn : n ≤ 64) : (H n input).length = n := by
  simp only [H, Spec.Blake2.blake2b, Spec.Blake2.blake2, List.length_take,
    wordList_length, Vector.length_toList]
  exact Nat.min_eq_left hn

theorem longHash_length (lastLen r : Nat) (v : List Byte)
    (hn : lastLen ≤ 64) (hv : v.length = 64) :
    (longHash lastLen r v).length = 32 * r + lastLen := by
  induction r generalizing v with
  | zero => simp only [longHash, H_length _ _ hn, Nat.mul_zero, Nat.zero_add]
  | succ r ih =>
    cases r with
    | zero => simp only [longHash, List.length_append, List.length_take,
        hv, H_length _ _ hn]; omega
    | succ r =>
      simp only [longHash, List.length_append, List.length_take, hv]
      rw [ih (H 64 v) (H_length 64 v (by decide))]
      omega

theorem longHash_bounds (n : Nat) (hn : 64 < n) :
    let r := (n + 31) / 32 - 2
    1 ≤ r ∧ 33 ≤ n - 32 * r ∧ n - 32 * r ≤ 64 ∧ 32 * r + (n - 32 * r) = n := by
  dsimp only
  omega

theorem hPrime_length (n : Nat) (input : List Byte) : (hPrime n input).length = n := by
  unfold hPrime
  split
  · exact H_length _ _ (by assumption)
  · rename_i hn
    have hb := longHash_bounds n (by omega)
    rw [longHash_length _ _ _ hb.2.2.1 (H_length 64 _ (by decide))]
    exact hb.2.2.2

theorem getD_append_zeros (m : List Byte) (n i : Nat) :
    (m ++ List.replicate n 0).getD i 0 = m.getD i 0 := by
  by_cases hi : i < m.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : m.length ≤ i),
      List.getElem?_eq_none (by omega : m.length ≤ i), Option.getD_none]
    simp only [List.getElem?_replicate]
    split <;> rfl

theorem padded_getD (m : List Byte) (i : Nat) :
    (Spec.Blake2.paddedData 64 [] m).getD i 0 = m.getD i 0 := by
  simp only [Spec.Blake2.paddedData, List.length_nil, Nat.lt_irrefl,
    ite_false, List.nil_append]
  split
  · rename_i he
    have hm : m = [] := by
      have hl : m.length = 0 := by
        simp only [Spec.Blake2.padZeros, List.length_append, List.length_replicate] at he
        omega
      exact List.eq_nil_of_length_eq_zero hl
    subst m
    simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none, List.getElem?_replicate]
    split <;> rfl
  · exact getD_append_zeros m _ i

theorem padded_blocks (m : List Byte) :
    (Spec.Blake2.paddedData 64 [] m).length / 128 - 1 = (m.length - 1) / 128 := by
  simp only [Spec.Blake2.paddedData, List.length_nil, Nat.lt_irrefl,
    ite_false, List.nil_append, Spec.Blake2.padZeros,
    List.length_append, List.length_replicate, Spec.Blake2.blockBytes]
  split <;> simp only [List.length_replicate, List.length_append]
  all_goals omega

theorem H_stream (n : Nat) (m : List Byte) :
    H n m = (Spec.Blake2.finalHash Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b n 0) m).take n := by
  simp only [H, Spec.Blake2.blake2b, Spec.Blake2.blake2,
    Spec.Blake2.finalHash, Spec.Blake2.compressed, Spec.Blake2.compressList,
    Spec.Blake2.blockBytes, List.length_nil, ite_true]
  simp only [show 16 * (64 / 8) = 128 from rfl, padded_getD, padded_blocks]

end VG.Proof.Argon2
