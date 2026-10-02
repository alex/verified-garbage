import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationPrepare

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.X86_64.FillIteration

open VG VG.X86_64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.X86_64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.X86_64.FillIteration.code
  refine WP.seq ((setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .rbp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.mxcsr.trans prepared.keeps.mxcsr, ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.regs .rsp (by decide), bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.r14] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.X86_64.FillIteration
