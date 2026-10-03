import VerifiedGarbage.Impl.Argon2.X86_64.InitialBody
import VerifiedGarbage.Proof.Argon2.X86_64.InitFill
import VerifiedGarbage.Proof.Argon2.X86_64.Initial

/-! Merged from `Proof.Argon2.X86_64.InitialMetadata`. -/
section
/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem Finished.rbp {s t : State} (h : Finished s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rbx {s t : State} (h : Finished s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rsp {s t : State} (h : Finished s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : Finished s t) (space : Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.rbp]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .rbp) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega) (by decide)

end VG.Proof.Argon2.X86_64.Initial
end

/-! Merged from `Proof.Argon2.X86_64.InitialBodyReady`. -/
section
/-! H₀ retains the allocation and parameter environment of complete derivation. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2

theorem hashed_environment {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word space 248 (by decide) (by decide)
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.rbp done.rsp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.rbp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.rbp, work]; exact e.addressLayout.frameWork
    · rw [done.rbp, done.rsp]; exact e.addressLayout.frameStack
    · rw [done.rsp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.rbp]; exact e.reads
  · rw [done.wr, done.rbp]; exact e.counterWrite
  · rw [done.wr, done.rbp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word space 240 (by decide) (by decide)).trans e.blocksWord
  · exact (done.frame_word space 72 (by decide) (by decide)).trans e.passesWord
  · exact (done.frame_word space 112 (by decide) (by decide)).trans e.variantWord
  · exact (done.frame_word space 184 (by decide) (by decide)).trans e.lanesWord

theorem hashed_output {s t : State} {p : Params} (h : InitFill.Ready p s) (space : Initial.Space s) (done : Initial.Finished s t) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word space 232 (by decide) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word space 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨h.output.positive, h.output.bound, ?_,
    (done.frame_word space 264 (by decide) (by decide)).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.rbp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.rsp, base]; exact h.output.stackInput
  · rw [done.rsp, output]; exact h.output.stackOutput
  · rw [done.rsp, work]; exact h.output.stackWork

theorem hashed_ready {s t : State} {p : Params} (h : InitFill.Ready p s)
    (space : Initial.Space s) (done : Initial.Finished s t) : InitFill.Ready p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word space 232 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word space 248 (by decide) (by decide)
  refine ⟨?_, hashed_environment h space done, hashed_output h space done, h.positive, ?_⟩
  · constructor
    · rw [base]
      exact h.initializing.space.same done.wr done.rbp done.rbx done.rsp
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.memoryRead
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.lanesRead
    · rw [done.rd, done.wr, done.rbp]; exact h.initializing.blocksRead
    · exact (done.frame_word space 232 (by decide) (by decide)).trans h.initializing.memoryWord |>.trans base.symm
    · exact (done.frame_word space 184 (by decide) (by decide)).trans h.initializing.lanesWord
    · exact (done.frame_word space 240 (by decide) (by decide)).trans h.initializing.blocksWord
    · exact (done.regs .r13 (by decide) (by decide) (by decide)).trans h.initializing.laneLength
  · rw [done.rbx, work]; exact h.scratch

end VG.Proof.Argon2.X86_64.InitialBody
end

/-! H₀, initialization, every filling pass, and finalization agree with derive. -/

namespace VG.Proof.Argon2.X86_64.InitialBody

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  hashSpace : Initial.Space s
  inputs : ∀ input ∈ Initial.inputs, Initial.InputReady s input.1 input.2
  header : Initial.headerBytes s = Proof.Argon2.initialHeader p
  filling : InitFill.Ready p s

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = derive p
    (Initial.inputBytes s passwordOffset passwordLenOffset)
    (Initial.inputBytes s saltOffset saltLenOffset)
    (Initial.inputBytes s secretOffset secretLenOffset)
    (Initial.inputBytes s adOffset adLenOffset)
  bp : t.gpr .rbp = s.gpr .rbp
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (InitFill.writes s p) s.mem t.mem

theorem hash_frame {s t : State} {p : Params} (h : InitFill.Ready p s) (done : Initial.Finished s t) :
    Frame (InitFill.writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [InitFill.writes], by
      rw [h.scratch]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.gpr .rsp) 24, by simp [InitFill.writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [InitFill.writes], Region.sub_prefix (by decide)⟩

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v)) s (Done s · p) := by
  unfold Impl.Argon2.X86_64.InitialBody.code
  refine WP.seq ((Initial.initialHash_ok v s h.hashSpace h.inputs p h.header).mono ?_)
  rintro a ⟨digest, hashed⟩
  refine (InitFill.code_ok v name a p (hashed_ready h.filling h.hashSpace hashed)).mono ?_
  intro t filled
  have base : FillKernel.matrix a = FillKernel.matrix s := hashed.frame_word h.hashSpace 232 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := hashed.frame_word h.hashSpace 248 (by decide) (by decide)
  have output : FinalOutput.output a = FinalOutput.output s := hashed.frame_word h.hashSpace 256 (by decide) (by decide)
  refine ⟨?_, filled.bp.trans hashed.rbp, filled.sp.trans hashed.rsp,
    filled.rd.trans hashed.rd, filled.wr.trans hashed.wr, ?_⟩
  · have result := filled.digest
    rw [output, hashed.rbp, digest, InitFill.result_derive] at result
    exact result
  · have frame := filled.frame
    rw [InitFill.writes_eq s a p hashed.rbp hashed.rsp base work output] at frame
    exact (hash_frame h.filling hashed).trans frame

end VG.Proof.Argon2.X86_64.InitialBody
