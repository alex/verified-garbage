import VerifiedGarbage.Spec.Argon2

/-! Expose the reviewed filling step's random word, matrix update and leakage log. -/

namespace VG.Proof.Argon2.FillStep

open VG.Spec.Argon2

def random (p : Params) (pass lane slice index : Nat) (blocks : Array Block) : Word :=
  if independent p pass slice then
    (addressBlock p pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))
  else
    (blocks[lane * p.laneLen + (slice * p.segmentLen + index + p.laneLen - 1) % p.laneLen]?.getD zeroBlock)[0]

def update (p : Params) (pass lane slice index : Nat) (blocks : Array Block) (word : Word) : Array Block :=
  let column := slice * p.segmentLen + index
  let current := lane * p.laneLen + column
  let prev := blocks[lane * p.laneLen + (column + p.laneLen - 1) % p.laneLen]?.getD zeroBlock
  let ref := reference p pass lane slice index word
  let other := blocks[ref.1 * p.laneLen + ref.2]?.getD zeroBlock
  let next := compress prev other
  blocks.set! current (if pass = 0 then next else xorBlock next (blocks[current]?.getD zeroBlock))

theorem not_skipped (pass slice index : Nat) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    ¬(pass = 0 ∧ slice = 0 ∧ index < 2) := by omega

theorem memory (p : Params) (pass lane slice index : Nat) (s : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    (fillBlock p pass slice lane index s).memory =
      update p pass lane slice index s.memory (random p pass lane slice index s.memory) := by
  rw [fillBlock, ite_eq_right (not_skipped pass slice index active)]
  rfl

theorem indices (p : Params) (pass lane slice index : Nat) (s : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    (fillBlock p pass slice lane index s).indices = if independent p pass slice then s.indices
      else reference p pass lane slice index (random p pass lane slice index s.memory) :: s.indices := by
  rw [fillBlock, ite_eq_right (not_skipped pass slice index active)]
  rfl

end VG.Proof.Argon2.FillStep
