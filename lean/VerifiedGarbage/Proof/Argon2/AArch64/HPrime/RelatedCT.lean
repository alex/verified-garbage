import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.BlocksCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.InitCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.UpdateCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FinalizeCT

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → FinalizeReady s
  keeps : ∀ s t, F s → Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ AgreeRegs publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : Related F s₁ s₂) (k₁ : Keeps s₁ t₁) (k₂ : Keeps s₂ t₂) : Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂,
    k₁.sp.trans (h.2.2.1.trans k₂.sp.symm), fun r hr => ?_⟩
  rw [k₁.regs _ (publicRegs_callee r hr) (publicRegs_not_link r hr), k₂.regs _ (publicRegs_callee r hr) (publicRegs_not_link r hr)]
  exact h.2.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (Keeps s₁) ∧ WP isa c s₂ (Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → Related F s₁ s₂) : RelCT isa P c (Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (init v.hash) (Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64) :
      InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply keeps_rel stable (init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2.2 _ (by decide), eq, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨init_keeps v s₁ (ready s₁ h.1 len),
      init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (finalize v.hash) (Related F) := by
  apply keeps_rel stable (finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2.2 _ (by decide), count, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨finalize_keeps v s₁ (stable.ready _ h.1), finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.AArch64.HPrime
