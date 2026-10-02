import VerifiedGarbage.Proof.Argon2.AArch64.FillCompress
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressOperationCT

/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : Ready s
  right : Ready t
  args : ∀ r ∈ [Reg.x0, .x1, .x6, .x19], s.gpr r = t.gpr r
  scratch : work s = work t
  counter : pass s = pass t
  sp : s.sp = t.sp

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    setup (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem prepared_public {s t a b : State} (h : CodeRelated s t)
    (ha : Prepared s a) (hb : Prepared t b) : Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .x6 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm), ha.sp.trans (h.sp.trans hb.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .x0 (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .x1 (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .x19 (by simp [loopRegs])).trans
      ((h.args .x19 (by simp)).trans (hb.regs .x19 (by simp [loopRegs])).symm)

theorem setup_public_rel : RelCT isa CodeRelated setup Related := by
  have trace := setup_rel.mono (P' := CodeRelated)
    (fun _ _ h => ⟨h.args .x19 (by simp), h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s h.left, setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel : RelCT isa CodeRelated code (fun s t => s.sp = t.sp) :=
  setup_public_rel.seq operation_rel

end VG.Proof.Argon2.AArch64.FillCompress
