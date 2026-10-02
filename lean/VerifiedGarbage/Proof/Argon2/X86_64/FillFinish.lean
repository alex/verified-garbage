import VerifiedGarbage.Impl.Argon2.X86_64.FillFinish
import VerifiedGarbage.Proof.Argon2.X86_64.FillFinishReady
import VerifiedGarbage.Proof.Argon2.X86_64.FinishStage

/-! The complete filling and finalization stages produce the reviewed final tag. -/

namespace VG.Proof.Argon2.X86_64.FillFinish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState
open VG.Spec.Blake2 (bytesAt)

structure Ready (p : Params) (s : State) : Prop where
  filling : FillIterations.Ready p 0 s
  finish : Finish.Ready p s
  positive : 0 < p.passes

def writes (s : State) (p : Params) : List Region := FillIterations.writes s p ++ Finish.writes s p

structure Done (s t : State) (p : Params) (state : FillState) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen =
    Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes state).memory
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params)
    (h : Ready p s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks state.memory) :
    WP isa (Impl.Argon2.X86_64.FillFinish.code name (HPrime.hash v)) s (Done s · p state) := by
  unfold Impl.Argon2.X86_64.FillFinish.code
  refine WP.seq ((FillIterations.loop_ok p.passes s p 0 h.filling state represented h.positive (Nat.zero_add _)).mono ?_)
  intro a filled
  refine (Finish.code_ok v name a p (finish_ready h.filling h.finish filled) _ filled.represented).mono ?_
  intro t finished
  have output : FinalOutput.output a = FinalOutput.output s := filled.frame_word h.filling 256 (by decide) (by decide)
  have work : FinalOutput.work a = FinalOutput.work s := filled.frame_word h.filling 248 (by decide) (by decide)
  have base : matrix a = matrix s := filled.matrix
  refine ⟨?_, fun r hr bx sl ix => (finished.regs r hr bx).trans (filled.regs r hr bx sl ix),
    finished.rd.trans filled.rd, finished.wr.trans filled.wr, ?_⟩
  · have digest := finished.digest
    rw [output] at digest; exact digest
  · have firstFrame : Frame (writes s p) s.mem a.mem := filled.frame.sub (by
      intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
    have lastFrame := finished.frame
    rw [Finish.writes, base, output, work,
      filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)] at lastFrame
    apply firstFrame.trans
    apply lastFrame.sub
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillFinish
