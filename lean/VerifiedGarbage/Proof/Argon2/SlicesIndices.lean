import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.LanesIndices

/-! Reference-log suffixes span slices with different public addressing modes. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def sliceReferences (p : Params) (pass slice : Nat) : Nat := p.lanes * segmentReferences p pass slice

def slicesReferences (p : Params) (pass start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sliceReferences p pass start + slicesReferences p pass (start + 1) n

theorem slices_indices_drop (p : Params) (pass start count : Nat) (state : FillState)
    (minimum : 2 ≤ p.segmentLen) :
    (slices p pass start count state).indices.drop (slicesReferences p pass start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [slices_succ, slicesReferences,
      show sliceReferences p pass start + slicesReferences p pass (start + 1) n =
        slicesReferences p pass (start + 1) n + sliceReferences p pass start from Nat.add_comm _ _,
      ← List.drop_drop, ih]
    exact lanes_indices_drop p pass start 0 p.lanes state minimum

theorem slices_first_lane_fold (p : Params) (pass start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (slices p pass start (count + 1) leftState).indices =
      (slices p pass start (count + 1) rightState).indices) :
    (lanes p pass start 0 p.lanes leftState).indices = (lanes p pass start 0 p.lanes rightState).indices := by
  have dropped := congrArg (List.drop (slicesReferences p pass (start + 1) count)) indices
  rw [slices_succ, slices_succ, slices_indices_drop p pass (start + 1) count _ minimum,
    slices_indices_drop p pass (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2
