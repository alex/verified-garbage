import VerifiedGarbage.Proof.Argon2.X86_64.FillSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillFinish

/-! Filling setup retains the final-call layout and establishes the reduction dimensions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem Prepared.finish_ready {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (outputReady : FinalOutput.Ready p s) (positive : 0 < p.passes) : FillFinish.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have base : ReductionState.matrix t = ReductionState.matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.words 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.words 248 (by decide) (by decide)
  obtain ⟨lane, slice, header⟩ := done.ready.filling.header
  have params := ready.environment.parameters
  refine ⟨done.ready, ⟨?_, ?_⟩, positive⟩
  · refine ⟨⟨params.lanesPositive, params.segment_bound.1, ?_, header.layout.frameRead 232 (by simp),
      header.layout.matrixWrite, header.layout.matrixFrame, header.laneLength⟩,
      params.lanesBound, header.layout.frameRead 184 (by simp), header.lanesWord⟩
    have blocks := Proof.Argon2.blocks_le_memory p
    have memory := params.memoryBound
    omega
  · refine ⟨outputReady.positive, outputReady.bound, ?_,
      (done.words 264 (by decide) (by decide)).trans outputReady.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact outputReady.reads
    · rw [base, done.rd, done.wr]; exact outputReady.input
    · rw [output, done.wr]; exact outputReady.outputWrite
    · rw [work, done.wr]; exact outputReady.workWrite
    · rw [base, work]; exact outputReady.inputWork
    · rw [output, work]; exact outputReady.outputWork
    · rw [sp, base]; exact outputReady.stackInput
    · rw [sp, output]; exact outputReady.stackOutput
    · rw [sp, work]; exact outputReady.stackWork

end VG.Proof.Argon2.X86_64.FillSetup
