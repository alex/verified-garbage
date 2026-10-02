import VerifiedGarbage.Proof.Argon2.Segment

/-! The first two cells of pass zero's first segment are already initialized. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def segmentStart (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem segment_first_two (p : Params) (lane : Nat) (state : FillState) :
    segment p 0 lane 0 0 2 state = state := by
  rw [segment_succ, segment_succ, segment_zero]
  simp only [fillBlock, Nat.reduceAdd, and_self, Nat.reduceLT, ite_true]

theorem segment_start (p : Params) (pass lane slice : Nat) (state : FillState) (minimum : 2 ≤ p.segmentLen) :
    segment p pass lane slice 0 p.segmentLen state =
      segment p pass lane slice (segmentStart pass slice) (p.segmentLen - segmentStart pass slice) state := by
  by_cases first : pass = 0 ∧ slice = 0
  · obtain ⟨rfl, rfl⟩ := first
    have append := segment_append p 0 lane 0 0 2 (p.segmentLen - 2) state
    rw [show 2 + (p.segmentLen - 2) = p.segmentLen by omega, segment_first_two] at append
    exact append
  · simp only [segmentStart, first, ite_false, Nat.sub_zero]

end VG.Proof.Argon2
