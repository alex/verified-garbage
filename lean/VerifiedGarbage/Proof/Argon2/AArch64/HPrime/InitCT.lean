import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 8).Disjoint ⟨s.gpr .x24, 192⟩

theorem init_keeps (v : Backend) (s : State) (h : InitReady s) :
    WP isa (init v.hash) s (Keeps s) :=
  (init_ok v s h.length h.work).mono fun _ ⟨_, regs, rd, wr, sp, frame⟩ =>
    ⟨regs, rd, wr, sp, init_frame _ _ frame⟩

theorem init_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → InitReady s₁ ∧ InitReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (init v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.initName) (k := Proof.Blake2.initAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    v.initCorrect v.initCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      · simp only [Proof.Blake2.initAArch64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen], h₁.sp.trans (sp.trans h₂.sp.symm)⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
