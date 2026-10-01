import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩

theorem init_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : InitReady s) :
    WP isa (init (hash v)) s (Keeps s) :=
  (init_ok v s h.length h.work h.stack).mono fun _ ⟨_, regs, rd, wr, frame⟩ =>
    ⟨regs, rd, wr, init_frame _ _ frame⟩

theorem init_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (init (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).initName) (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    Proof.Blake2.X86_64.Stream.initB_correct Proof.Blake2.X86_64.Stream.initB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work p₂.stack
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, ?_⟩
      · simp only [Proof.Blake2.initX86_64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen]⟩
      · rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
