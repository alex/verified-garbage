import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Fixed
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelatedCT

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : FixedArgs s t offset size) : Keeps s t := by
  refine ⟨fun r hr _ => ?_, h.rd, h.wr, h.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : FinalizeReady s)
    (h : FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .x3).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).spBound, (ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .x3).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.x24]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.x24]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  · rw [k.sp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Backend) (s : State) (offset size : Nat)
    (ready : FinalizeReady s) (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed v.hash offset size) s (Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetBound (by omega)).mono fun u hu => ?_)
  exact (update_keeps v u (fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Backend) (offset size : Nat)
    (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (absorbFixed v.hash offset size) (Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨fixedArgs_ok s₁ offset size offsetBound (by omega),
      fixedArgs_ok s₂ offset size offsetBound (by omega)⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related F σ₁ σ₂ ∧ FixedArgs σ₁ s₁ offset size ∧ FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2.2 .x24 (by decide)
      have sp := hp.2.2.1
      exact ⟨fixed_ready (stable.ready _ hp.1) h₁ lo hi, fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.x24, h₂.keeps.x24, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.sp, h₂.keeps.sp, sp]⟩
  exact keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) offsetBound lo hi,
      absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) offsetBound lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
