import VerifiedGarbage.Proof.Argon2.Lanes

/-! Slice folds expose the reviewed filling pass without changing its specification. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def slices (p : Params) (pass start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fun state slice => lanes p pass slice 0 p.lanes state) state

theorem slices_zero (p : Params) (pass start : Nat) (state : FillState) : slices p pass start 0 state = state := rfl

theorem slices_succ (p : Params) (pass start count : Nat) (state : FillState) :
    slices p pass start (count + 1) state = slices p pass (start + 1) count (lanes p pass start 0 p.lanes state) := by
  unfold slices
  rw [List.range'_succ, List.foldl_cons]

theorem slices_pass (p : Params) (pass : Nat) (state : FillState) : slices p pass 0 4 state = fillPass p state pass := by
  unfold slices lanes segment fillPass
  simp only [List.range_eq_range']

end VG.Proof.Argon2
