import VerifiedGarbage.Proof.Argon2.Segment
import VerifiedGarbage.Proof.Argon2.FillStep

/-! The reference log exposes exactly one coordinate per dependent active cell. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem segment_indices_drop (p : Params) (pass lane slice start count : Nat) (state : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start) (dependent : independent p pass slice = false) :
    (segment p pass lane slice start count state).indices.drop count = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [segment_succ]
    have next : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start + 1 := by omega
    rw [← List.drop_drop, ih (start + 1) (fillBlock p pass slice lane start state) next]
    rw [FillStep.indices p pass lane slice start state active]
    simp only [dependent, Bool.false_eq_true, ite_false, List.drop_succ_cons, List.drop_zero]

theorem segment_first_reference (p : Params) (pass lane slice start count : Nat)
    (leftState rightState : FillState) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start)
    (indices : (segment p pass lane slice start (count + 1) leftState).indices =
      (segment p pass lane slice start (count + 1) rightState).indices)
    (dependent : independent p pass slice = false) :
    reference p pass lane slice start (FillStep.random p pass lane slice start leftState.memory) =
      reference p pass lane slice start (FillStep.random p pass lane slice start rightState.memory) := by
  have dropped := congrArg (List.drop count) indices
  rw [segment_succ, segment_succ,
    segment_indices_drop p pass lane slice (start + 1) count _ (by omega) dependent,
    segment_indices_drop p pass lane slice (start + 1) count _ (by omega) dependent,
    FillStep.indices p pass lane slice start leftState active,
    FillStep.indices p pass lane slice start rightState active] at dropped
  simp only [dependent, Bool.false_eq_true, ite_false] at dropped
  exact (List.cons.inj dropped).1

end VG.Proof.Argon2
