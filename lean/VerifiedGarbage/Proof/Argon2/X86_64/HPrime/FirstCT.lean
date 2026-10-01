import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.InputCT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Length

/-! # H′: constant time of the initial length-prefixed hash -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi)

theorem chooseFirst_rel : RelCT isa (Related FirstReady) chooseLength
    (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (chooseLength_rel.mono (P' := Related FirstReady)
    (fun _ _ hp => hp.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ _ => ⟨chooseLength_ok s₁, chooseLength_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨pub, s₁, s₂, hp, ⟨len₁, k₁⟩, ⟨_, k₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_, pub _ (List.mem_cons_self ..)⟩
  rw [len₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : min (s₁.gpr .r15).toNat 64 < 2 ^ 64)]
  have := hp.1.positive
  omega

theorem inputCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) s fun t =>
      Keeps s t ∧ t.gpr .rsi = s.gpr .r13 + 4 := by
  refine wp_mov fun a ha _ _ => wp_addi fun t ht => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.other r hn).trans (ha.other r hn)
    · rw [ht.mem, ha.mem]; exact Frame.refl _ _
  · rw [ht.gpr, ha.gpr]; rfl

theorem inputCount_rel :
    RelCT isa (Related FirstReady) (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)])
      (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) (by taint_decide)).wpDep
    (fun s₁ s₂ _ => ⟨inputCount_ok s₁, inputCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_⟩
  rw [c₁, c₂, hp.2.2 .r13 (by decide)]

theorem first_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related FirstReady) (first (hash v)) (Related FirstReady) :=
  chooseFirst_rel.seq ((stable_init_rel v first_stable).seq
    ((absorbFixed_rel v 832 4 (by decide) (by decide) ⟨_, by taint_decide⟩ first_stable).seq
    ((absorbInput_rel v).seq (inputCount_rel.seq (stable_finalize_rel v first_stable)))))

end VG.Proof.Argon2.X86_64.HPrime
