import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure FinalizeReady (s : State) : Prop where
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  refine ⟨by rw [k.sp]; exact h.spBound, ?_, ?_⟩
  · rw [k.wr, k.x24]; exact h.work
  · rw [k.sp, k.x24]; exact h.stack

theorem finalize_keeps (v : Backend) (s : State) (h : FinalizeReady s) :
    WP isa (finalize v.hash) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.spBound h.work h.stack
  refine WP.callF (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b) v.finalizeCorrect
    pre cover writes ?_ (by rw [v.ok.finalizeDepth]; decide)
  intro t rd wr sp frame regs _
  refine ⟨fun r hr h30 => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr h30).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply finalize_frame
    simpa only [v.ok.finalizeDepth, hu.sp, hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (finalize v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.finalizeName) (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    v.finalizeCorrect v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.spBound p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.spBound p₂.work p₂.stack
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
