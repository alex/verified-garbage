import VerifiedGarbage.Proof.Argon2.Segment

/-! Lane folds used by the public filling loops. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def lanes (p : Params) (pass slice start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state lane => segment p pass lane slice 0 p.segmentLen state) state

theorem lanes_zero (p : Params) (pass slice start : Nat) (state : FillState) :
    lanes p pass slice start 0 state = state := rfl

theorem lanes_succ (p : Params) (pass slice start count : Nat) (state : FillState) :
    lanes p pass slice start (count + 1) state =
      lanes p pass slice (start + 1) count (segment p pass start slice 0 p.segmentLen state) := by
  unfold lanes
  rw [List.range'_succ, List.foldl_cons]

end VG.Proof.Argon2
