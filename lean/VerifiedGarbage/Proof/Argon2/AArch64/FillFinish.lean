import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.AArch64.FinishReady
import VerifiedGarbage.Impl.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady
import VerifiedGarbage.Proof.Argon2.Serialization

/-! Merged from `Proof.Argon2.AArch64.FinishStage`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FinalOutput`. -/
section
/-! The generic H′ call produces exactly the reviewed final Argon2 tag. -/

namespace VG.Proof.Argon2.AArch64.FinalOutput

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (output s) p.tagLen = finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨output s, p.tagLen⟩, ⟨work s, 16384⟩, below s.sp 16] s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (block : blockAt s.mem (ReductionState.matrix s) = Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) :
    WP isa (Impl.Argon2.AArch64.FinalOutput.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.FinalOutput.code
  refine WP.seq ((args_ok s h.reads).mono ?_)
  intro a args
  have length := args.outputLength.trans h.tagWord
  refine (FinalCall.hPrime_call_ok v name p.tagLen a (args.ready h) args.inputLength length).mono ?_
  intro t called
  refine ⟨?_, fun r hr => (called.regs r hr).trans (args.regs r hr), called.sp.trans args.keeps.sp, called.rd.trans args.keeps.rd,
    called.wr.trans args.keeps.wr, ?_⟩
  · have input : bytesAt a.mem (a.gpr .x0) 1024 =
        serialize (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock) := by
      rw [args.keeps.mem, args.input, ← Proof.Argon2.serialize_blockAt, block]
    rw [Proof.Argon2.finish_reduction]
    have digest := called.digest
    rw [args.output, input] at digest
    exact digest
  · have frame := called.frame
    rw [args.output, args.work, args.keeps.sp, args.keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.AArch64.FinalOutput
end

/-! The complete reviewed finish computation, with its enclosing frame and ABI obligations. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

def writes (s : State) (p : Params) : List Region :=
  [⟨matrix s, 1024⟩, ⟨FinalOutput.output s, p.tagLen⟩,
    ⟨FinalOutput.work s, 16384⟩, below s.sp 16]

structure Done (s t : State) (p : Params) (memory : Array Block) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = Spec.Argon2.finish p memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa (Impl.Argon2.AArch64.Finish.code name v.hash) s (Done s · p memory) := by
  unfold Impl.Argon2.AArch64.Finish.code
  refine WP.seq ((FinalReduction.code_ok s p h.reduction memory represented).mono ?_)
  intro a reduced
  refine (FinalOutput.code_ok v name a p (output_ready h reduced) memory reduced.represented.accumulator).mono ?_
  intro t written
  have output : FinalOutput.output a = FinalOutput.output s := frame_word h.reduction reduced 256 (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := frame_word h.reduction reduced 248 (by decide)
  refine ⟨?_, fun r hr bx => (written.regs r hr).trans (reduced.regs r hr bx),
    written.sp.trans reduced.sp, written.rd.trans reduced.rd, written.wr.trans reduced.wr, ?_⟩
  · have digest := written.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := reduced.frame.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, by simp [writes], fun _ h => h⟩)
    have lastFrame := written.frame
    rw [output, work, reduced.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.Finish
end

/-! Merged from `Proof.Argon2.AArch64.FillFinishReady`. -/
section
/-! The complete filling loop retains the original final-call allocations and public metadata. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem finish_ready {s t : State} {p : Params} {state : FillState}
    (filling : FillIterations.Ready p 0 s) (ready : Finish.Ready p s)
    (done : FillIterations.Finished s t p state) : Finish.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)
  have sp := done.sp
  have base : matrix t = matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word filling 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word filling 248 (by decide) (by decide)
  constructor
  · have a := ready.reduction.allocation
    refine ⟨⟨a.positive, a.minimum, a.bound, ?_, ?_, ?_, ?_⟩, ready.reduction.lanesBound, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact a.read
    · rw [base, done.wr]; exact a.write
    · rw [base, bp]; exact a.frame
    · exact (done.regs .x20 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans a.length
    · rw [done.rd, done.wr, bp]; exact ready.reduction.lanesRead
    · exact (done.frame_word filling 184 (by decide) (by decide)).trans ready.reduction.lanesWord
  · refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
      (done.frame_word filling 264 (by decide) (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact ready.output.stackMinimum
    · rw [done.rd, done.wr, bp]; exact ready.output.reads
    · rw [base, done.rd, done.wr]; exact ready.output.input
    · rw [output, done.wr]; exact ready.output.outputWrite
    · rw [work, done.wr]; exact ready.output.workWrite
    · rw [base, work]; exact ready.output.inputWork
    · rw [output, work]; exact ready.output.outputWork
    · rw [sp, base]; exact ready.output.stackInput
    · rw [sp, output]; exact ready.output.stackOutput
    · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.FillFinish
end

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.AArch64.FillFinish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.AArch64.FillFinish.code name v.hash) s (Done s · p state) := by
  unfold Impl.Argon2.AArch64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.sp.trans filled.sp, finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.sp] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.AArch64.FillFinish
