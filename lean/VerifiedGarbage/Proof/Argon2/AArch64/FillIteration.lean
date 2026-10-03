import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration
import VerifiedGarbage.Proof.Argon2.AArch64.FillSlices

/-! Merged from `Proof.Argon2.AArch64.FillIterationPrepare`. -/
section
/-! Start a pass at slice zero regardless of its incoming lane and slice coordinates. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (pass : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass 0 0
  header : ∃ lane slice, FillHeader.Ready p pass lane slice s

structure Prepared (s t : State) (p : Params) (pass : Nat) : Prop where
  ready : FillSlice.Ready p pass 0 t
  keeps : Divide.Keeps [.x22] s t

theorem setup_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) :
    WP isa (.block Impl.Argon2.AArch64.FillIteration.setup) s (Prepared s · p pass) := by
  refine (SegmentSetup.register_ok s .x22 0 (by decide)).mono ?_
  rintro t ⟨sliceWord, keeps⟩
  obtain ⟨lane, slice, header⟩ := h.header
  obtain ⟨old, words⟩ := header.words
  have next : FillHeader.Ready p pass lane 0 t := header.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact keeps.regs _ (by decide))
    keeps.sp keeps.mem keeps.rd keeps.wr ((keeps.regs .x24 (by decide)).trans words.laneWord) sliceWord
  exact ⟨⟨h.parameters, lane, next⟩, keeps⟩

end VG.Proof.Argon2.AArch64.FillIteration
end

/-! One complete filling pass against the reviewed specification. -/

namespace VG.Proof.Argon2.AArch64.FillIteration

open VG VG.AArch64 VG.Spec.Argon2

theorem code_ok (s : State) (p : Params) (pass : Nat) (h : Ready p pass s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillIteration.code s (FillSlices.Finished s · p pass (fillPass p state pass)) := by
  unfold Impl.Argon2.AArch64.FillIteration.code
  refine WP.seq ((setup_ok s p pass h).mono ?_)
  intro a prepared
  have bp := prepared.keeps.regs .x19 (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by unfold FillKernel.matrix; rw [prepared.keeps.mem, bp]
  have work : AddressCalls.work a = AddressCalls.work s := by unfold AddressCalls.work; rw [prepared.keeps.mem, bp]
  have representedA : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks state.memory := by
    rw [prepared.keeps.mem, base]; exact represented
  refine (FillSlices.pass_ok a p pass prepared.ready state representedA).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.matrix.trans base, finished.work.trans work, finished.header,
    finished.rd.trans prepared.keeps.rd, finished.wr.trans prepared.keeps.wr, ?_,
    finished.sp.trans prepared.keeps.sp, ?_⟩
  · have frame := finished.frame
    rw [FillBlock.writes, base, work, prepared.keeps.sp, bp, prepared.keeps.mem] at frame
    exact frame
  · intro r hr bx sl ix
    have ne : r ∉ [Reg.x22] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sl
    exact (finished.regs r hr bx sl ix).trans (prepared.keeps.regs r ne)

end VG.Proof.Argon2.AArch64.FillIteration
