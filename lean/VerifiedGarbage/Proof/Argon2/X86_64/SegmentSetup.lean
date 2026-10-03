import VerifiedGarbage.Proof.Argon2.SegmentStart
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupCheck`. -/
section
/-! Check the prepared index before entering the nonempty segment loop. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

theorem Prepared.of_keeps {p : Params} {pass lane slice : Nat} {s a t : State}
    (h : Prepared s a p pass lane slice) (k : Divide.Keeps [] a t) : Prepared s t p pass lane slice := by
  have bp := k.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix a := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work a := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.context.of_keeps (k.mono (by decide)), base.trans h.matrix, work.trans h.work,
    ?_, k.rd.trans h.rd, k.wr.trans h.wr, ?_, k.mxcsr.trans h.mxcsr⟩
  · intro r hr ne; exact (k.regs r (by simp)).trans (h.regs r hr ne)
  · rw [k.mem]; exact h.frame

theorem check_prepared_ok {p : Params} {pass lane slice : Nat} {s a : State}
    (h : Prepared s a p pass lane slice) : WP isa (.block check) a fun t =>
      Prepared s t p pass lane slice ∧ t.cf = decide (start pass slice < p.segmentLen) := by
  refine (check_ok a).mono ?_
  rintro t ⟨flag, keeps⟩
  have minimum := h.context.parameters.segment_bound
  refine ⟨h.of_keeps keeps, ?_⟩
  rw [flag, h.context.position.index, h.context.position.segmentLength,
    ReferenceMap.word_nat (start pass slice) (Nat.lt_of_le_of_lt (start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem finished_prepared {p : Params} {pass lane slice : Nat} {s a t : State} {state : FillState}
    (prepared : Prepared s a p pass lane slice) (finished : FillSegment.Finished a t p pass lane slice state) :
    FillSegment.Finished s t p pass lane slice state := by
  refine ⟨finished.represented, finished.matrix.trans prepared.matrix, finished.work.trans prepared.work,
    finished.position, finished.layout, finished.cache, finished.matrixWork, finished.passWord, finished.lanesWord,
    ?_, finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans prepared.mxcsr⟩
  · intro r hr ne; exact (finished.regs r hr ne).trans (prepared.regs r hr ne)
  · have firstFrame : Frame (FillBlock.writes s p) s.mem a.mem := by
      apply prepared.frame.sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨off (s.gpr .rbp) 8, 16⟩, by simp [FillBlock.writes], Region.sub_prefix (by decide)⟩
    have rest := finished.frame
    rw [FillBlock.writes, prepared.matrix, prepared.work,
      prepared.regs .rsp (by simp [calleeSaved]) (by decide),
      prepared.regs .rbp (by simp [calleeSaved]) (by decide)] at rest
    exact firstFrame.trans rest

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Fill one complete segment, including the initialized prefix and empty suffix. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

theorem code_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : Ready p pass lane slice s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa code s (FillSegment.Finished s · p pass lane slice
      (Proof.Argon2.segment p pass lane slice 0 p.segmentLen state)) := by
  rw [Proof.Argon2.segment_start p pass lane slice state h.parameters.segment_bound.1]
  change WP isa code s (FillSegment.Finished s · p pass lane slice
    (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) state))
  unfold code
  refine WP.seq ((prepare_ok s p pass lane slice h).mono ?_)
  intro a prepared
  refine WP.seq ((check_prepared_ok prepared).mono ?_)
  rintro b ⟨prepared, flag⟩
  have matrix := prepared.represents h state.memory represented
  refine WP.ite (decide (start pass slice < p.segmentLen)) (by simp only [eval, flag]) ?_ ?_
  · intro taken
    have bound := of_decide_eq_true taken
    have active := prepared.context.activate bound (start_active pass slice)
    refine (FillSegment.loop_ok (p.segmentLen - start pass slice) b p pass lane slice (start pass slice) 0
      active state matrix (by omega) (by omega)).mono ?_
    intro t finished
    exact finished_prepared prepared finished
  · intro skipped
    have bound := of_decide_eq_false skipped
    have minimum := h.parameters.segment_bound.1
    have last : start pass slice = p.segmentLen := by have := start_le pass slice p.segmentLen minimum; omega
    have finished : FillSegment.Finished b b p pass lane slice state :=
      ⟨matrix, rfl, rfl, last ▸ prepared.context.position, prepared.context.layout,
        ⟨0, prepared.context.cache⟩, prepared.context.matrixWork, prepared.context.cache.words.passWord,
        prepared.context.lanesWord, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
    rw [last, Nat.sub_self, Proof.Argon2.segment_zero]
    exact WP.block_nil (finished_prepared prepared finished)

end VG.Proof.Argon2.X86_64.SegmentSetup
