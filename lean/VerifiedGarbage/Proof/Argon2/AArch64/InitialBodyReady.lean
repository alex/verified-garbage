import VerifiedGarbage.Proof.Argon2.AArch64.InitialMetadata
import VerifiedGarbage.Proof.Argon2.AArch64.InitFill

/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.x19 done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.x19]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.x19, work]; exact e.addressLayout.frameWork
    · rw [done.x19, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.x19]; exact e.reads
  · rw [done.wr, done.x19]; exact e.counterWrite
  · rw [done.wr, done.x19]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word space 240 (by decide) (by decide)).trans e.blocksWord
  · exact (done.frame_word space 72 (by decide) (by decide)).trans e.passesWord
  · exact (done.frame_word space 112 (by decide) (by decide)).trans e.variantWord
  · exact (done.frame_word space 184 (by decide) (by decide)).trans e.lanesWord

theorem hashed_output {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
    (done.frame_word space 264 (by decide) (by decide)).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.x19]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem hashed_ready {s t : State} {p : Params} (h : InitFill.Ready p s)
    (space : Initial.Space s) (done : Initial.Finished s t) : InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, hashed_environment h space done, hashed_output h space done, h.positive, ?_⟩
  · constructor
    · rw [base]
      exact h.initializing.space.same done.wr done.x19 done.x24 done.sp
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.memoryRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.lanesRead
    · rw [done.rd, done.wr, done.x19]; exact h.initializing.blocksRead
    · exact (done.frame_word space 232 (by decide) (by decide)).trans h.initializing.memoryWord |>.trans base.symm
    · exact (done.frame_word space 184 (by decide) (by decide)).trans h.initializing.lanesWord
    · exact (done.frame_word space 240 (by decide) (by decide)).trans h.initializing.blocksWord
    · exact (done.regs .x21 (by decide) (by decide) (by decide)).trans h.initializing.laneLength
  · rw [done.x24, work]; exact h.scratch

end VG.Proof.Argon2.AArch64.InitialBody
