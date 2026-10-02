import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.ChainCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)

def OutputCompared (s t : State) : Prop := Related OutputReady s t ∧ s.gpr .x9 = t.gpr .x9 ∧
  s.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0

theorem OutputCompared.short {s t : State} (h : OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some true) :
    (s.gpr .x23).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .x23).toNat < 65 := by omega
  simp [eval, State.read, h.2.2, n] at flag

theorem OutputCompared.long {s t : State} (h : OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some false) :
    Related LoopReady s t := by
  have n : 65 ≤ (s.gpr .x23).toNat := by
    by_contra hn
    have n : (s.gpr .x23).toNat < 65 := by omega
    simp [eval, State.read, h.2.2, n] at flag
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2.2 .x23 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Backend) :
    RelCT isa OutputCompared (.ite (.nonzero .x .x9) (.block []) (chain v.hash))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.addImm .x .x1 .x23 0]) s fun t =>
    Keeps s t ∧ t.gpr .x1 = s.gpr .x23 := by
  refine wp_mov fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  exact Keeps.of_upd ht (by decide)

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64)
      (.block [.addImm .x .x1 .x23 0])
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  let P := fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64
  have ct := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.addImm .x .x1 .x23 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨lastCount_ok s₁, lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Backend) :
    RelCT isa (Related LoopReady) (extendDigest v.hash) (Related OutputReady) :=
  emit_rel.seq ((compare_rel output_stable).seq
    ((maybeChain_rel v).seq (lastCount_rel.seq (next_rel v output_stable))))

theorem finishOutput_rel (v : Backend) :
    RelCT isa (Related OutputReady) (finishOutput v.hash) (AgreeRegs publicRegs) := by
  have branches : RelCT isa OutputCompared (.ite (.nonzero .x .x9) (.block []) (extendDigest v.hash)) (Related OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (compare_rel output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.AArch64.HPrime
