import VerifiedGarbage.Proof.Argon2.X86_64.InitialBody

/-! The complete body depends on the frame, allocation, and computed lane length. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

structure SameFrame (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem SameFrame.word {s t : State} (k : SameFrame s t) (d : Nat) :
    Initial.wordAt t d = Initial.wordAt s d := by
  unfold Initial.wordAt; rw [k.mem, k.bp]

theorem SameFrame.inputBytes {s t : State} (k : SameFrame s t) (po lo : Nat) :
    Initial.inputBytes t po lo = Initial.inputBytes s po lo := by
  unfold Initial.inputBytes; rw [k.word po, k.word lo, k.mem]

theorem SameFrame.hashSpace {s t : State} (k : SameFrame s t)
    (h : Initial.Space s) : Initial.Space t := by
  constructor
  · rw [k.bx, k.wr]; exact h.work
  · rw [k.sp, k.bx]; exact h.stackWork
  · rw [k.bp, k.bx]; exact h.frameWork
  · rw [k.bp, k.sp]; exact h.frameStack
  · rw [k.rd, k.wr, k.bp]; exact h.readable
  · rw [k.wr, k.bp]; exact h.output

theorem SameFrame.input {s t : State} (k : SameFrame s t) {po lo : Nat}
    (h : Initial.InputReady s po lo) : Initial.InputReady t po lo := by
  have word : ∀ d, Initial.wordAt t d = Initial.wordAt s d := by
    intro d; unfold Initial.wordAt; rw [k.mem, k.bp]
  have region : Initial.inputRegion t po lo = Initial.inputRegion s po lo := by
    unfold Initial.inputRegion; rw [word po, word lo]
  refine ⟨k.hashSpace h.space, h.pointerSlot, h.lengthSlot, h.pointerBound,
    h.lengthBound, ?_, ?_, ?_, ?_⟩
  · rw [word lo]; exact h.length
  · rw [region, k.rd, k.wr]; exact h.cover
  · rw [region, k.bx]; exact h.work
  · rw [region, k.sp]; exact h.stack

theorem SameFrame.output {s t : State} (k : SameFrame s t) {p : Params}
    (h : FinalOutput.Ready p s) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := by
    unfold ReductionState.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  have output : FinalOutput.output t = FinalOutput.output s := by
    unfold FinalOutput.output; rw [k.mem, k.bp]
  refine ⟨h.positive, h.bound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.rd, k.wr, k.bp]; exact h.reads
  · rw [k.mem, k.bp]; exact h.tagWord
  · rw [base, k.rd, k.wr]; exact h.input
  · rw [output, k.wr]; exact h.outputWrite
  · rw [work, k.wr]; exact h.workWrite
  · rw [base, work]; exact h.inputWork
  · rw [output, work]; exact h.outputWork
  · rw [k.sp, base]; exact h.stackInput
  · rw [k.sp, output]; exact h.stackOutput
  · rw [k.sp, work]; exact h.stackWork

theorem SameFrame.filling {s t : State} (k : SameFrame s t) {p : Params}
    (h : InitFill.Ready p s) (laneLength : t.gpr .r13 = BitVec.ofNat 64 p.laneLen) :
    InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.bp]
  have work : FinalOutput.work t = FinalOutput.work s := by
    unfold FinalOutput.work; rw [k.mem, k.bp]
  refine ⟨?_, h.environment.of_state k.bp k.sp k.mem k.rd k.wr,
    k.output h.output, h.positive, ?_⟩
  · constructor
    · rw [base]; exact h.initializing.space.same k.wr k.bp k.bx k.sp
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.memoryRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.lanesRead
    · rw [k.rd, k.wr, k.bp]; exact h.initializing.blocksRead
    · unfold Initial.wordAt; rw [k.mem, k.bp, base]; exact h.initializing.memoryWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.lanesWord
    · unfold Initial.wordAt; rw [k.mem, k.bp]; exact h.initializing.blocksWord
    · exact laneLength
  · rw [k.bx, work]; exact h.scratch

theorem Ready.of_state {s t : State} {p : Params} (h : Ready p s)
    (k : SameFrame s t) (laneLength : t.gpr .r13 = BitVec.ofNat 64 p.laneLen) : Ready p t := by
  refine ⟨k.hashSpace h.hashSpace, fun input hi => k.input (h.inputs input hi), ?_,
    k.filling h.filling laneLength⟩
  have header : Initial.headerBytes t = Initial.headerBytes s := by
    unfold Initial.headerBytes
    simp only [Initial.headerValue, Initial.wordAt, k.mem, k.bp]
  exact header.trans h.header

end VG.Proof.Argon2.X86_64.InitialBody
