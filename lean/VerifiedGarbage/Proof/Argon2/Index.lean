import VerifiedGarbage.Proof.Argon2.Dimensions

/-! # Bounds for Argon2's reference-block selection -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Every executed block has a nonempty reference area. The first segment
of pass zero uses its own lane and skips the two initialized blocks. -/
theorem referenceCount_pos (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (sameLane : Bool)
    (hfirst : pass = 0 → slice = 0 → sameLane = true ∧ 2 ≤ index) :
    0 < referenceCount p pass slice index sameLane := by
  have hseg := segmentLen_ge_two p hl hm
  have hlen := laneLen_segments p hl
  unfold referenceCount
  split
  · next hp =>
    by_cases hs : slice = 0
    · obtain ⟨hsame, hi⟩ := hfirst hp hs
      simp only [hs, hsame, ite_eq_left, Nat.zero_mul, Nat.zero_add]
      omega
    · have hmul := Nat.mul_le_mul_right p.segmentLen (show 1 ≤ slice by omega)
      simp only [Nat.one_mul] at hmul
      split
      · omega
      · split <;> omega
  · split
    · omega
    · split <;> omega

/-- The reference area never includes more than one lane. -/
theorem referenceCount_lt_laneLen (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass slice index : Nat) (sameLane : Bool)
    (hs : slice < 4) (hi : index < p.segmentLen) :
    referenceCount p pass slice index sameLane < p.laneLen := by
  have hseg := segmentLen_ge_two p hl hm
  have hlen := laneLen_segments p hl
  have hcol := column_lt p hl hs hi
  unfold referenceCount
  split
  · split
    · omega
    · split <;> omega
  · split
    · omega
    · split <;> omega

theorem reference_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    (reference p pass lane slice index random).1 * p.laneLen +
      (reference p pass lane slice index random).2 < p.blocks := by
  obtain ⟨hrl, hrc⟩ := reference_bounds p hl hm pass lane slice index random hlane
  exact cell_lt p hl hrl hrc

end VG.Proof.Argon2
