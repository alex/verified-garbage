import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.FixedCT

/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem count64_ok (s : State) : WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
    Keeps s t ∧ t.gpr .rsi = 64 := by
  refine wp_mov32i fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov32 .rsi (.imm 64)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (next (hash v)) (Related F) :=
  (stable_init_rel v stable).seq
    ((absorbFixed_rel v 768 64 (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((count64_rel stable).seq (stable_finalize_rel v stable)))

end VG.Proof.Argon2.X86_64.HPrime
