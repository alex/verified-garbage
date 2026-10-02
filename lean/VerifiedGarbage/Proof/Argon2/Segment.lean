import VerifiedGarbage.Spec.Argon2

/-! Segment folds used by the filling-loop invariant. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segment (p : Params) (pass lane slice start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state index => fillBlock p pass slice lane index state) state

theorem segment_zero (p : Params) (pass lane slice start : Nat) (state : FillState) :
    segment p pass lane slice start 0 state = state := rfl

theorem segment_succ (p : Params) (pass lane slice start count : Nat) (state : FillState) :
    segment p pass lane slice start (count + 1) state =
      segment p pass lane slice (start + 1) count (fillBlock p pass slice lane start state) := by
  unfold segment
  rw [List.range'_succ, List.foldl_cons]

theorem segment_append (p : Params) (pass lane slice start a b : Nat) (state : FillState) :
    segment p pass lane slice start (a + b) state =
      segment p pass lane slice (start + a) b (segment p pass lane slice start a state) := by
  unfold segment
  rw [← List.range'_append_1, List.foldl_append]

end VG.Proof.Argon2
