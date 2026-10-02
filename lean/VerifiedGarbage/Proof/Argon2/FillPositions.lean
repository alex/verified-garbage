import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.Offset

/-! Bounds for every block address used by the filling loop. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem previous_column_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (column : Nat) :
    (column + p.laneLen - 1) % p.laneLen < p.laneLen := by
  have seg := segmentLen_ge_two p hl hm
  have lanes := laneLen_segments p hl
  exact Nat.mod_lt _ (by omega)

theorem cell_bytes (p : Params) (hl : 0 < p.lanes) {lane column : Nat}
    (hlane : lane < p.lanes) (hcolumn : column < p.laneLen) :
    (lane * p.laneLen + column) * 1024 + 1024 ≤ p.blocks * 1024 := by
  have cell := cell_lt p hl hlane hcolumn
  have scaled := Nat.mul_le_mul_right 1024 (show lane * p.laneLen + column + 1 ≤ p.blocks by omega)
  simpa only [Nat.add_mul, Nat.one_mul] using scaled

theorem current_cell_lt (p : Params) (hl : 0 < p.lanes) {lane slice index : Nat}
    (hlane : lane < p.lanes) (hslice : slice < 4) (hindex : index < p.segmentLen) :
    lane * p.laneLen + (slice * p.segmentLen + index) < p.blocks :=
  cell_lt p hl hlane (column_lt p hl hslice hindex)

theorem previous_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) {lane column : Nat} (hlane : lane < p.lanes) :
    lane * p.laneLen + ((column + p.laneLen - 1) % p.laneLen) < p.blocks :=
  cell_lt p hl hlane (previous_column_lt p hl hm column)

theorem reference_cell_lt (p : Params) (hl : 0 < p.lanes)
    (hm : 8 * p.lanes ≤ p.memory) (pass lane slice index : Nat) (random : Word)
    (hlane : lane < p.lanes) :
    let ref := reference p pass lane slice index random
    ref.1 * p.laneLen + ref.2 < p.blocks := by
  obtain ⟨laneBound, columnBound⟩ := reference_bounds p hl hm pass lane slice index random hlane
  exact cell_lt p hl laneBound columnBound

theorem cell_contains (base : VG.Addr) (p : Params) (hl : 0 < p.lanes)
    (hm : p.memory < 2 ^ 32) {lane column : Nat}
    (hlane : lane < p.lanes) (hcolumn : column < p.laneLen) :
    (⟨base, p.blocks * 1024⟩ : VG.Region).Contains
      (base + BitVec.ofNat 64 ((lane * p.laneLen + column) * 1024)) 1024 := by
  have bytes := cell_bytes p hl hlane hcolumn
  have blocks : p.blocks < 2 ^ 32 := Nat.lt_of_le_of_lt (blocks_le_memory p) hm
  have total : p.blocks * 1024 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocks (by decide : 0 < 1024)) (by decide +kernel)
  exact VG.Offset.contains_base base
    (d := (lane * p.laneLen + column) * 1024) (n := 1024) (k := p.blocks * 1024)
    bytes (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) bytes) total)

end VG.Proof.Argon2
