import VerifiedGarbage.Proof.Argon2.AArch64.FillKernel
import VerifiedGarbage.Proof.Argon2.Matrix

/-! The filling step updates exactly one cell of the specification's block array. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

def currentIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + currentColumn p slice index

def previousIndex (p : Params) (lane slice index : Nat) : Nat :=
  lane * p.laneLen + previousColumn p slice index

def referenceIndex (s : State) (p : Params) (pass lane slice index : Nat) : Nat :=
  let ref := Spec.Argon2.reference p pass lane slice index (s.gpr .x0)
  ref.1 * p.laneLen + ref.2

def nextBlock (s : State) (p : Params) (pass lane slice index : Nat) (blocks : Array Block) : Block :=
  let next := Spec.Argon2.compress (blocks[previousIndex p lane slice index]?.getD zeroBlock)
    (blocks[referenceIndex s p pass lane slice index]?.getD zeroBlock)
  if pass = 0 then next else xorBlock next (blocks[currentIndex p lane slice index]?.getD zeroBlock)

theorem Done.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (matrix s) p.blocks
      (blocks.set! (currentIndex p lane slice index) (nextBlock s p pass lane slice index blocks)) := by
  have currentBound := Proof.Argon2.current_cell_lt p ready.bounds.lanesPositive
    ready.bounds.laneBound ready.bounds.sliceBound ready.bounds.indexBound
  have previousBound := Proof.Argon2.previous_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum ready.bounds.laneBound (column := currentColumn p slice index)
  have referenceBound := Proof.Argon2.reference_cell_lt p ready.bounds.lanesPositive
    ready.bounds.memoryMinimum pass lane slice index (s.gpr .x0) ready.bounds.laneBound
  apply represented.update (currentIndex p lane slice index) currentBound (nextBlock s p pass lane slice index blocks)
  · have block := done.block
    change blockAt t.mem (Proof.Argon2.matrixCell (matrix s) (currentIndex p lane slice index)) = _ at block
    have prev := represented.block (previousIndex p lane slice index) previousBound
    have other := represented.block (referenceIndex s p pass lane slice index) referenceBound
    have old := represented.block (currentIndex p lane slice index) currentBound
    change blockAt s.mem (previous s p lane slice index) = _ at prev
    change blockAt s.mem (referenced s p pass lane slice index) = _ at other
    change blockAt s.mem (current s p lane slice index) = _ at old
    rw [prev, other, old] at block
    exact block
  · intro j hj different
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have blocksBound := Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) ready.bounds.memoryBound
      exact Proof.Argon2.matrixCell_disjoint _ p.blocks j (currentIndex p lane slice index)
        (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right blocksBound (by decide)) (by decide)) hj currentBound different
    · exact ready.layout.matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact ready.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)
    · exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hj)).sub_right
        (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.AArch64.FillKernel
