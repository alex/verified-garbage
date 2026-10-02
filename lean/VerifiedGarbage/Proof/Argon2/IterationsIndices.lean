import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Argon2.SlicesIndices

/-! Recover each pass's reviewed reference log from the complete filling log. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def passReferences (p : Params) (pass : Nat) : Nat := slicesReferences p pass 0 4

def iterationsReferences (p : Params) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => passReferences p start + iterationsReferences p (start + 1) n

theorem pass_indices_drop (p : Params) (pass : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (fillPass p state pass).indices.drop (passReferences p pass) = state.indices := by
  rw [← slices_pass p pass state]
  exact slices_indices_drop p pass 0 4 state minimum

theorem iterations_indices_drop (p : Params) (start count : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    (iterations p start count state).indices.drop (iterationsReferences p start count) = state.indices := by
  induction count generalizing start state with
  | zero => rfl
  | succ n ih =>
    rw [iterations_succ, iterationsReferences,
      show passReferences p start + iterationsReferences p (start + 1) n =
        iterationsReferences p (start + 1) n + passReferences p start from Nat.add_comm _ _,
      ← List.drop_drop, ih, pass_indices_drop p start state minimum]

theorem iterations_first_pass (p : Params) (start count : Nat) (leftState rightState : FillState)
    (minimum : 2 ≤ p.segmentLen)
    (indices : (iterations p start (count + 1) leftState).indices =
      (iterations p start (count + 1) rightState).indices) :
    (fillPass p leftState start).indices = (fillPass p rightState start).indices := by
  have dropped := congrArg (List.drop (iterationsReferences p (start + 1) count)) indices
  rw [iterations_succ, iterations_succ, iterations_indices_drop p (start + 1) count _ minimum,
    iterations_indices_drop p (start + 1) count _ minimum] at dropped
  exact dropped

end VG.Proof.Argon2
