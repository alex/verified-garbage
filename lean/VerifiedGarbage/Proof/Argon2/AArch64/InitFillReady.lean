import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitDone
import VerifiedGarbage.Proof.Argon2.AArch64.FillSetupFinish

/-! Retain the filling environment and final-call layout across memory initialization. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  initializing : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen s
  environment : FillSetup.Environment p s
  output : FinalOutput.Ready p s
  positive : 0 < p.passes
  scratch : s.gpr .x24 = FinalOutput.work s

theorem initialized_environment {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.bp done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.bp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.bp, work]; exact e.addressLayout.frameWork
    · rw [done.bp, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.bp]; exact e.reads
  · rw [done.wr, done.bp]; exact e.counterWrite
  · rw [done.wr, done.bp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word h.initializing.space 240 (by decide) (Or.inr (by decide))).trans e.blocksWord
  · exact (done.frame_word h.initializing.space 72 (by decide) (Or.inr (by decide))).trans e.passesWord
  · exact (done.frame_word h.initializing.space 112 (by decide) (Or.inr (by decide))).trans e.variantWord
  · exact (done.frame_word h.initializing.space 184 (by decide) (Or.inr (by decide))).trans e.lanesWord

theorem initialized_output {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
    (done.frame_word h.initializing.space 264 (by decide) (Or.inr (by decide))).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.bp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem initialized_setup {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Ready p t := by
  have params := h.environment.parameters
  have product : p.laneLen ≤ p.lanes * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ p.lanes from params.lanesPositive)
  refine ⟨initialized_environment h done, ?_, done.stride⟩
  have bound := h.initializing.space.bound
  have bytes := Nat.mul_le_mul_left 1024 product
  omega

theorem initialized_represents {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
      (initMemory p (Spec.Blake2.bytesAt s.mem (s.gpr .x19) 64)).memory := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  rw [base]
  have segments := Proof.Argon2.laneLen_segments p h.environment.parameters.lanesPositive
  have minimum := h.environment.parameters.segment_bound.1
  exact done.initialized.represents h.environment.parameters.lanesPositive (by omega)

end VG.Proof.Argon2.AArch64.InitFill
