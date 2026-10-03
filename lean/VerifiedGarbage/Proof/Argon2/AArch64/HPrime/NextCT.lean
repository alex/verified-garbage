import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FixedCT

/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem count64_ok (s : State) : WP isa (.block [.movz .x .x1 64 0]) s fun t =>
    Keeps s t ∧ t.gpr .x1 = 64 := by
  refine wp_movz fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr _ => ?_, ht.rd, ht.wr, ht.sp, ?_⟩
  · have hn : r ≠ .x1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.movz .x .x1 64 0])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.movz .x .x1 64 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (next v.hash) (Related F) :=
  (stable_init_rel v stable).seq
    ((absorbFixed_rel v 768 64 (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((count64_rel stable).seq (stable_finalize_rel v stable)))

end VG.Proof.Argon2.AArch64.HPrime
