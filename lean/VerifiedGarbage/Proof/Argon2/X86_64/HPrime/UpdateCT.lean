import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure UpdateReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩
  dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

theorem update_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : UpdateReady s) :
    WP isa (update (hash v)) s (Keeps s) := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := update_call_hyps s u hu h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.call (k := Proof.Blake2.updateX86_64 Spec.Blake2.b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2)
  · apply update_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, hu.other .rsp (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → UpdateReady s₁ ∧ UpdateReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (update (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := UpdateArgs) fun s₁ s₂ _ => ⟨updateArgs_ok s₁, updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).updateName) (k := Proof.Blake2.updateX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ UpdateArgs σ₁ s₁ ∧ UpdateArgs σ₂ s₂)
    v.update_correct v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := update_call_hyps σ₁ s₁ h₁ p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := update_call_hyps σ₂ s₂ h₂ p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
