import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.OutputCT

/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem chainBody_rel (v : Backend) :
    RelCT isa (Related LoopReady)
      (.seq (.block [.movz .x .x1 64 0])
        (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ s₁.gpr .x9 = s₂.gpr .x9 ∧
        s₁.gpr .x9 = if (s₁.gpr .x23).toNat < 65 then 1 else 0) :=
  (count64_init_rel loop_stable).seq ((next_rel v loop_stable).seq
    (emit_rel.seq (compare_rel output_stable)))

theorem chainStep_ready (v : Backend) (s : State) (h : LoopReady s) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])))) s (ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .x23).toNat by have := h.2; omega)
  exact chainStep_ok v s space.spBound ⟨by have := h.2; omega, h.1.bound⟩ space.work space.out space.sep space.stackWork

theorem chain_rel (v : Backend) :
    RelCT isa (Related LoopReady) (chain v.hash)
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => Related LoopReady s₁ s₂ ∧ (s₁.gpr .x23).toNat = n
  have step (n : Nat) := ((chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨chainStep_ready v s₁ hp.1.1, chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain v.hash)
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, State.read, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, hn] at flag
    intro flag
    have lo : 65 ≤ (t₁.gpr .x23).toNat := by
      by_contra h
      have lt : (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, lt] at flag
    have remain : (t₁.gpr .x23).toNat = (s₁.gpr .x23).toNat - 32 := by
      rw [h₁.remaining, sub32_nat _ (by have := hp.1.1.2; omega)]
    refine ⟨(t₁.gpr .x23).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .x23).toNat := hp.1.1.2
      have count : (s₁.gpr .x23).toNat = m := hp.2
      omega
    · rw [← ready.2.2.2 .x23 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .x23).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
