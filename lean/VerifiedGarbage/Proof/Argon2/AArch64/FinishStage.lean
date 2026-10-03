import VerifiedGarbage.Impl.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.FinishReady
import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutput

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
