import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperationCT

/-! Compose the setup trace with compression and the full block write. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure CodeRelated (s t : State) : Prop where
  left : Ready s
  right : Ready t
  args : ∀ r ∈ [Reg.rdi, .rsi, .r10, .rsp, .rbp], s.gpr r = t.gpr r
  scratch : work s = work t
  counter : pass s = pass t

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    setup (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem prepared_public {s t a b : State} (h : CodeRelated s t)
    (ha : Prepared s a) (hb : Prepared t b) : Related a b := by
  refine ⟨ha.ready, hb.ready, ?_, ha.dest.trans ((h.args .r10 (by simp)).trans hb.dest.symm),
    ha.counter.trans (h.counter.trans hb.counter.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha.left.trans ((h.args .rdi (by simp)).trans hb.left.symm)
  · exact ha.right.trans ((h.args .rsi (by simp)).trans hb.right.symm)
  · exact ha.output.trans ((congrArg (· + (4096 : Addr)) h.scratch).trans hb.output.symm)
  · exact ha.scratch.trans (h.scratch.trans hb.scratch.symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      ((h.args .rsp (by simp)).trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      ((h.args .rbp (by simp)).trans (hb.regs .rbp (by simp [calleeSaved])).symm)

theorem setup_public_rel : RelCT isa CodeRelated setup Related := by
  have trace := setup_rel.mono (P' := CodeRelated)
    (fun _ _ h => h.args .rbp (by simp)) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨setup_ok s h.left, setup_ok t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel : RelCT isa CodeRelated code (fun _ _ => True) :=
  setup_public_rel.seq operation_rel

end VG.Proof.Argon2.X86_64.FillCompress
