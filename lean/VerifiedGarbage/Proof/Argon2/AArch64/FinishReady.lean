import VerifiedGarbage.Proof.Argon2.AArch64.FinalReduction
import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)
  have sp := done.sp
  have output : FinalOutput.output t = FinalOutput.output s := frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := frame_word ready.reduction done 248 (by decide)
  refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
    (frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact ready.output.stackMinimum
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.Finish
