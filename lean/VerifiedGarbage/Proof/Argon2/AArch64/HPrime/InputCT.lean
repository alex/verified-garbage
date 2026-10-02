import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.NextCT
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Space

/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure OutputReady (s : State) : Prop where
  space : Space s (s.gpr .x23).toNat
  positive : 1 ≤ (s.gpr .x23).toNat
  bound : (s.gpr .x23).toNat < 2 ^ 32

theorem output_stable : Stable OutputReady where
  ready _ h := ⟨h.space.spBound, h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .x23 (by decide) (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends OutputReady s where
  length : (s.gpr .x21).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩

theorem first_stable : Stable FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .x20 (by decide) (by decide)
    have len := k.regs .x21 (by decide) (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.x24]; exact h.dataWork
    · rw [ptr, len, k.sp]; exact h.stackData

theorem input_ready {s t : State} (ready : FirstReady s) (h : InputArgs s t) : UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).spBound,
    (first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.x24, k.sp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.sp]; exact ready.stackData

theorem absorbInput_keeps (v : Backend) (s : State) (h : FirstReady s) :
    WP isa (absorbInput v.hash) s (Keeps s) := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  exact (update_keeps v u (input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Backend) :
    RelCT isa (Related FirstReady) (absorbInput v.hash) (Related FirstReady) := by
  have args := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := InputArgs) fun s₁ s₂ _ => ⟨inputArgs_ok s₁, inputArgs_ok s₂⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related FirstReady σ₁ σ₂ ∧ InputArgs σ₁ s₁ ∧ InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨input_ready hp.1 h₁, input_ready hp.2.1 h₂,
        by rw [h₁.keeps.x24, h₂.keeps.x24]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.keeps.sp, h₂.keeps.sp]; exact hp.2.2.1⟩
  exact keeps_rel first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbInput_keeps v s₁ hp.1, absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
