import VerifiedGarbage.Proof.Argon2.Lanes
import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.SegmentStart

/-! Recover each segment's reference log from the complete lane fold. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segmentReferences (p : Params) (pass slice : Nat) : Nat :=
  if independent p pass slice then 0 else p.segmentLen - segmentStart pass slice

theorem fillBlock_independent_indices (p : Params) (pass lane slice index : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (fillBlock p pass slice lane index state).indices = state.indices := by
  unfold fillBlock
  split
  · rfl
  · simp only [mode, ite_true]

theorem segment_independent_indices (p : Params) (pass lane slice start count : Nat) (state : FillState)
    (mode : independent p pass slice = true) : (segment p pass lane slice start count state).indices = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [segment_succ, ih, fillBlock_independent_indices p pass lane slice start state mode]

theorem segment_references_drop (p : Params) (pass lane slice : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (segment p pass lane slice 0 p.segmentLen state).indices.drop (segmentReferences p pass slice) = state.indices := by
  cases mode : independent p pass slice
  · rw [segment_start p pass lane slice state minimum]
    change (segment p pass lane slice (segmentStart pass slice) (p.segmentLen - segmentStart pass slice) state).indices.drop
      (if independent p pass slice then 0 else p.segmentLen - segmentStart pass slice) = state.indices
    simp only [mode, Bool.false_eq_true, ite_false]
    apply segment_indices_drop _ _ _ _ _ _ _ _ mode
    unfold segmentStart; split <;> omega
  · rw [segment_independent_indices p pass lane slice 0 p.segmentLen state mode]
    simp only [segmentReferences, mode, ite_true, List.drop_zero]

theorem lanes_indices_drop (p : Params) (pass slice start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (lanes p pass slice start count state).indices.drop (count * segmentReferences p pass slice) = state.indices := by
  induction count generalizing start state with
  | zero => rw [Nat.zero_mul, lanes_zero, List.drop_zero]
  | succ n ih =>
    rw [lanes_succ, Nat.add_mul, Nat.one_mul, ← List.drop_drop,
      ih, segment_references_drop p pass start slice state minimum]

theorem lanes_first_segment (p : Params) (pass slice start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (lanes p pass slice start (count + 1) leftState).indices =
      (lanes p pass slice start (count + 1) rightState).indices) :
    (segment p pass start slice 0 p.segmentLen leftState).indices =
      (segment p pass start slice 0 p.segmentLen rightState).indices := by
  have dropped := congrArg (List.drop (count * segmentReferences p pass slice)) indices
  rw [lanes_succ, lanes_succ, lanes_indices_drop p pass slice (start + 1) count _ minimum,
    lanes_indices_drop p pass slice (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2
