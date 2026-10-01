import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.ChainCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)

def Compared (s t : State) : Prop := Related OutputReady s t ∧ s.cf = t.cf ∧
  s.cf = some (decide ((s.gpr .r15).toNat < 65))

theorem Compared.short {s t : State} (h : Compared s t) (flag : isa.eval .b s = some true) :
    (s.gpr .r15).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .r15).toNat < 65 := by omega
  simp only [eval, h.2.2, n, decide_false] at flag
  contradiction

theorem Compared.long {s t : State} (h : Compared s t) (flag : isa.eval .b s = some false) :
    Related LoopReady s t := by
  have n : 65 ≤ (s.gpr .r15).toNat := by
    by_contra hn
    have n : (s.gpr .r15).toNat < 65 := by omega
    simp only [eval, h.2.2, n, decide_true] at flag
    contradiction
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2 .r15 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Compared (.ite .b (.block []) (chain (hash v)))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.mov .rsi (.reg .r15)]) s fun t =>
    Keeps s t ∧ t.gpr .rsi = s.gpr .r15 := by
  refine wp_mov fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64)
      (.block [.mov .rsi (.reg .r15)])
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  let P := fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64
  have ct := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rsi (.reg .r15)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨lastCount_ok s₁, lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related LoopReady) (extendDigest (hash v)) (Related OutputReady) :=
  emit_rel.seq ((compare_rel output_stable).seq
    ((maybeChain_rel v).seq (lastCount_rel.seq (next_rel v output_stable))))

theorem finishOutput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related OutputReady) (finishOutput (hash v)) (AgreeRegs publicRegs) := by
  have branches : RelCT isa Compared (.ite .b (.block []) (extendDigest (hash v))) (Related OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (compare_rel output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.X86_64.HPrime
