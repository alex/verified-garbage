import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.OutputCT

/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem chainBody_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady)
      (.seq (.block [.mov32 .rsi (.imm 64)])
        (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) :=
  (count64_init_rel loop_stable).seq ((next_rel v loop_stable).seq
    (emit_rel.seq (compare_rel output_stable)))

theorem chainStep_ready (v : Proof.Blake2.X86_64.Backend) (s : State) (h : LoopReady s) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)])))) s (ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .r15).toNat by have := h.2; omega)
  exact chainStep_ok v s space.work space.out space.sep space.stackWork

theorem chain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady) (chain (hash v))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => Related LoopReady s₁ s₂ ∧ (s₁.gpr .r15).toNat = n
  have step (n : Nat) := ((chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨chainStep_ready v s₁ hp.1.1, chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain (hash v))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .r15).toNat < 65 := by omega
      simp only [eval, value, hn, decide_false, Option.map_some, Bool.not_false] at flag
      contradiction
    intro flag
    have lo : 65 ≤ (t₁.gpr .r15).toNat := by
      by_contra h
      have lt : (t₁.gpr .r15).toNat < 65 := by omega
      simp only [eval, value, lt, decide_true, Option.map_some, Bool.not_true] at flag
      contradiction
    have remain : (t₁.gpr .r15).toNat = (s₁.gpr .r15).toNat - 32 := by
      rw [h₁.remaining, sub32_nat _ (by have := hp.1.1.2; omega)]
    refine ⟨(t₁.gpr .r15).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .r15).toNat := hp.1.1.2
      have count : (s₁.gpr .r15).toNat = m := hp.2
      omega
    · rw [← ready.2.2 .r15 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .r15).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
