import VerifiedGarbage.Proof.Argon2.AArch64.FinishReady
import VerifiedGarbage.Impl.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputCT

/-! Complete finalization has a public trace for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params)
    (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) (Impl.Argon2.AArch64.Finish.code name v.hash)
      (fun _ _ => True) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq reduceA outputA =>
    cases eb with
    | seq reduceB outputB =>
      have related : ReductionInit.Related p leftMemory rightMemory s t :=
        ⟨hp.left.reduction, hp.right.reduction, hp.bases, hp.stacks, hp.matrices, hp.leftMatrix, hp.rightMatrix⟩
      obtain ⟨reduceTrace, _⟩ := FinalReduction.code_rel p hp.left.reduction.allocation.positive
        leftMemory rightMemory _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, doneA⟩ := FinalReduction.code_ok s p hp.left.reduction leftMemory hp.leftMatrix
      obtain ⟨_, sb, runB, doneB⟩ := FinalReduction.code_ok t p hp.right.reduction rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have finalRelated : FinalOutput.Related p _ _ :=
        ⟨output_ready hp.left doneA, output_ready hp.right doneB,
          (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
            (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm),
          (doneA.sp).trans
            (hp.stacks.trans (doneB.sp).symm),
          doneA.base.trans (hp.matrices.trans doneB.base.symm),
          (frame_word hp.left.reduction doneA 256 (by decide)).trans
            (hp.outputs.trans (frame_word hp.right.reduction doneB 256 (by decide)).symm),
          (frame_word hp.left.reduction doneA 248 (by decide)).trans
            (hp.works.trans (frame_word hp.right.reduction doneB 248 (by decide)).symm)⟩
      obtain ⟨outputTrace, _⟩ := FinalOutput.code_rel v name p _ _ _ _ _ _ finalRelated outputA outputB
      exact ⟨by rw [reduceTrace, outputTrace], trivial⟩

end VG.Proof.Argon2.AArch64.Finish
