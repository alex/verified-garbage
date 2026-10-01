import VerifiedGarbage.Spec.Argon2

/-! # Bounds for Argon2's rounded memory matrix -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem laneLen_eq (p : Params) (hl : 0 < p.lanes) :
    p.laneLen = 4 * (p.memory / (4 * p.lanes)) := by
  unfold Params.laneLen Params.blocks
  rw [Nat.mul_comm 4 p.lanes, Nat.mul_assoc, Nat.mul_div_cancel_left _ hl]

theorem segmentLen_eq (p : Params) (hl : 0 < p.lanes) :
    p.segmentLen = p.memory / (4 * p.lanes) := by
  unfold Params.segmentLen
  rw [laneLen_eq p hl, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]

theorem laneLen_segments (p : Params) (hl : 0 < p.lanes) :
    p.laneLen = 4 * p.segmentLen := by
  rw [laneLen_eq p hl, segmentLen_eq p hl]

theorem blocks_lanes (p : Params) (hl : 0 < p.lanes) :
    p.blocks = p.lanes * p.laneLen := by
  rw [laneLen_eq p hl]
  unfold Params.blocks
  rw [Nat.mul_comm 4 p.lanes, Nat.mul_assoc]

theorem blocks_le_memory (p : Params) : p.blocks ≤ p.memory :=
  Nat.mul_div_le _ _

theorem segmentLen_ge_two (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) : 2 ≤ p.segmentLen := by
  rw [segmentLen_eq p hl, Nat.le_div_iff_mul_le (by omega : 0 < 4 * p.lanes)]
  omega

theorem column_lt (p : Params) (hl : 0 < p.lanes) {slice index : Nat}
    (hs : slice < 4) (hi : index < p.segmentLen) :
    slice * p.segmentLen + index < p.laneLen := by
  have h := Nat.mul_le_mul_right p.segmentLen (show slice + 1 ≤ 4 by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  rw [laneLen_segments p hl]
  omega

theorem cell_lt (p : Params) (hl : 0 < p.lanes) {lane column : Nat}
    (hlane : lane < p.lanes) (hc : column < p.laneLen) :
    lane * p.laneLen + column < p.blocks := by
  have h := Nat.mul_le_mul_right p.laneLen (show lane + 1 ≤ p.lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  rw [blocks_lanes p hl]
  omega

theorem reference_bounds (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    (reference p pass lane slice index random).1 < p.lanes ∧
      (reference p pass lane slice index random).2 < p.laneLen := by
  have hseg := segmentLen_ge_two p hl hm
  have hlen := laneLen_segments p hl
  unfold reference
  constructor
  · split
    · exact hlane
    · exact Nat.mod_lt _ hl
  · exact Nat.mod_lt _ (by omega)

end VG.Proof.Argon2
