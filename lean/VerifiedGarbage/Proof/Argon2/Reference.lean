import VerifiedGarbage.Proof.Argon2.Dimensions

/-! # Bounds for the quadratic reference-window mapping in RFC 9106 §3.4.2 -/

namespace VG.Proof.Argon2

theorem reference_square_bound (j : Nat) (hj : j < 2 ^ 32) : j * j < 2 ^ 64 := by
  exact Nat.lt_of_lt_of_eq (Nat.mul_self_lt_mul_self hj) (by decide)

theorem reference_scaled_bound (j : Nat) (hj : j < 2 ^ 32) :
    j * j / 2 ^ 32 < 2 ^ 32 := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).mpr
  exact Nat.lt_of_lt_of_eq (reference_square_bound j hj) (by decide)

theorem reference_product_bound (count j : Nat) (hc : count < 2 ^ 32)
    (hj : j < 2 ^ 32) : count * (j * j / 2 ^ 32) < 2 ^ 64 := by
  exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt hc (reference_scaled_bound j hj))
    (by decide)

theorem reference_scale_lt_count (count j : Nat) (hc : 0 < count) (hj : j < 2 ^ 32) :
    count * (j * j / 2 ^ 32) / 2 ^ 32 < count := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).mpr
  exact Nat.mul_lt_mul_of_pos_left (reference_scaled_bound j hj) hc

theorem reference_relative_bound (count j : Nat) (hc : 0 < count) :
    count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32 < count := by
  omega

open VG.Spec.Argon2

theorem reference_count_lt_lane (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (same : Bool)
    (hs : slice < 4) (hi : index < p.segmentLen) :
    referenceCount p pass slice index same < p.laneLen := by
  have seg := segmentLen_ge_two p hl hm
  have len := laneLen_segments p hl
  have column := column_lt p hl hs hi
  unfold referenceCount
  by_cases first : pass = 0
  · rw [ite_eq_left first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega
  · rw [ite_eq_right first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega

theorem reference_count_positive (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (same : Bool)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (firstLane : pass = 0 → slice = 0 → same = true) :
    0 < referenceCount p pass slice index same := by
  have seg := segmentLen_ge_two p hl hm
  have len := laneLen_segments p hl
  unfold referenceCount
  by_cases first : pass = 0
  · rw [ite_eq_left first]
    by_cases zero : slice = 0
    · simp only [firstLane first zero, zero, Nat.zero_mul, ite_true]
      omega
    · have mul := Nat.mul_le_mul_right p.segmentLen (show 1 ≤ slice by omega)
      rw [Nat.one_mul] at mul
      cases same
      · simp only [Bool.false_eq_true, ite_false]
        split <;> omega
      · simp only [ite_true]
        omega
  · rw [ite_eq_right first]
    cases same
    · simp only [Bool.false_eq_true, ite_false]
      split <;> omega
    · simp only [ite_true]
      omega

theorem reference_count_32 (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (memoryBound : p.memory < 2 ^ 32)
    (pass slice index : Nat) (same : Bool) (hs : slice < 4) (hi : index < p.segmentLen) :
    referenceCount p pass slice index same < 2 ^ 32 := by
  have laneBlocks := Nat.le_mul_of_pos_left p.laneLen hl
  rw [← blocks_lanes p hl] at laneBlocks
  exact Nat.lt_of_lt_of_le (reference_count_lt_lane p hl hm pass slice index same hs hi)
    (Nat.le_trans laneBlocks (Nat.le_trans (blocks_le_memory p) (Nat.le_of_lt memoryBound)))

theorem reference_wrap (sum q : Nat) (bound : sum < 2 * q) :
    sum % q = if sum < q then sum else sum - q := by
  by_cases small : sum < q
  · rw [ite_eq_left small, Nat.mod_eq_of_lt small]
  · rw [ite_eq_right small, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Argon2
