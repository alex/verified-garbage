import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FinalizeReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : FinalizeReady s) (k : Keeps s t) : FinalizeReady t := by
  constructor
  · rw [k.wr, k.rbx]; exact h.work
  · rw [k.rsp, k.rbx]; exact h.stack

theorem finalize_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : FinalizeReady s) :
    WP isa (finalize (hash v)) s (Keeps s) := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := finalize_call_hyps s u hu h.work h.stack
  refine WP.call (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply finalize_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, hu.other .rsp (by decide) (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → FinalizeReady s₁ ∧ FinalizeReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (finalize (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := FinalizeArgs) fun s₁ s₂ _ => ⟨finalizeArgs_ok s₁, finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).finalizeName) (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ FinalizeArgs σ₁ s₁ ∧ FinalizeArgs σ₂ s₂)
    v.finalize_correct v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := finalize_call_hyps σ₁ s₁ h₁ p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := finalize_call_hyps σ₂ s₂ h₂ p₂.work p₂.stack
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
