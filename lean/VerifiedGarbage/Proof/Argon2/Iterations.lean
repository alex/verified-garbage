import VerifiedGarbage.Spec.Argon2

/-! Pass folds used by the outer filling-loop invariant. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def iterations (p : Params) (start count : Nat) (state : FillState) : FillState :=
  (List.range' start count).foldl (fillPass p) state

theorem iterations_zero (p : Params) (start : Nat) (state : FillState) : iterations p start 0 state = state := rfl

theorem iterations_succ (p : Params) (start count : Nat) (state : FillState) :
    iterations p start (count + 1) state = iterations p (start + 1) count (fillPass p state start) := by
  unfold iterations
  rw [List.range'_succ, List.foldl_cons]

theorem iterations_fill (p : Params) (password salt secret ad : List Byte) :
    iterations p 0 p.passes (initMemory p (initialHash p password salt secret ad)) = fill p password salt secret ad := by
  unfold iterations fill
  rw [List.range_eq_range']

end VG.Proof.Argon2
