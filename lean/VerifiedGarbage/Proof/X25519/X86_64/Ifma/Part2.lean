import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1

/-!
# X25519 on x86-64 with AVX512_IFMA: stages 2 and 3 of an iteration

Untrusted: everything here is checked by Lean. From `(AA, BB, DA, CB)` in
the lanes of `ymm0–ymm4`, stage 2 and its product leave `(x₃', t, x₂', a24 E)`
there (and its first operand, with `AA` and `E`, in `OPV`); stage 3 and its
product then leave `(x₂', z₂', x₃', z₃')`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

theorem lanes_keep {s s' : State} {r0 : Nat} (h : ∀ r < 16, r0 ≤ r → r < r0 + 5 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)
    (hr : r0 + 5 ≤ 16) : ∀ l < 4, ∀ i < 5, lanes s' r0 l i = lanes s r0 l i := fun l hl i hi => by
  simp only [lanes]; rw [h (r0 + i) (by omega) (by omega) (by omega) l hl]

theorem le_kbv {x : Nat} (i : Nat) (h : x < 2 ^ 61) : x ≤ kbv i := by simp only [kbv]; split <;> omega

/-- Stage 2 and its product. -/
theorem part2_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block (stage2 ++ mul4 OPV)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61 ∧ slotv s'.mem base OPV l i < 2 ^ 52) ∧
      fe5 (slotv s'.mem base OPV 2) = fe5 (lanes s 0 0) ∧
      fe5 (slotv s'.mem base OPV 3) = fe5 (lanes s 0 0) - fe5 (lanes s 0 1) ∧
      fe5 (lanes s' 0 0) = (fe5 (lanes s 0 2) + fe5 (lanes s 0 3)) * (fe5 (lanes s 0 2) + fe5 (lanes s 0 3)) ∧
      fe5 (lanes s' 0 1) = (fe5 (lanes s 0 2) - fe5 (lanes s 0 3)) * (fe5 (lanes s 0 2) - fe5 (lanes s 0 3)) ∧
      fe5 (lanes s' 0 2) = fe5 (lanes s 0 0) * fe5 (lanes s 0 1) ∧
      fe5 (lanes s' 0 3) = (fe5 (lanes s 0 0) - fe5 (lanes s 0 1)) * Spec.X25519.a24 := by
  have hr := hs.rdi
  simp only [stage2, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s2a_wp hr (scr_ctx hs) hk hy) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2.1)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have e₂ := lanes_keep (s := s₁) (s' := s₂) (r0 := 0) (fun r hr h1 h2 l hl => k₂ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₂.rdi (scr_ctx hs₂) hk₂.c fun l hl i hi => by
      rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.2)
    fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ := scr_of hs₂ (vm_gpr v₃) (vm_wr v₃)
  have e₃ := lanes_keep (s := s₂) (s' := s₃) (r0 := 5) (fun r hr h1 h2 l hl => k₃ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (s2b_wp hs₃.rdi (scr_ctx hs₃)) fun s₄ ⟨g₄, r₄, w₄, o₄, u₄, _⟩ => ?_
  have hs₄ := scr_of hs₃ g₄ w₄
  have b5 : ∀ l < 4, ∀ i < 5, lanes s₃ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [e₃ l hl i hi]; exact (u₂ l hl i hi).2
  refine WP.mono (mul4_wp (a := OPV) (by decide) (mulS_eq _ _) (mulV_nat) mulV_ok mulV_keep mulV_st
    hs₄.rdi (scr_ctx hs₄) (fun l hl i hi => by rw [(u₄ l hl i hi).1]; exact b5 l hl i hi)
    (fun l hl i hi => by rw [(u₄ l hl i hi).2]; exact (u₃ l hl i hi).2))
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  have K : Kept base s s₅ :=
    ((((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans
      ⟨g₄, r₄, w₄, o₄.mono (by decide) (by decide)⟩).trans (Kept.vm v₅ m₅)
  -- the operands
  have fV : ∀ l < 4, fe5 (slotv s₅.mem base OPV l) = fe5 (fun i => opV (lanes s 0) l i) := fun l hl => by
    rw [m₅, fe5_congr (fun i hi => (u₄ l hl i hi).1), fe5_congr (fun i hi => e₃ l hl i hi),
      fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2.1; omega)]
    exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have fW : ∀ l < 4, fe5 (lanes s₄ 5 l) = fe5 (fun i => opW (lanes s 0) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₄ l hl i hi).2), fe5_congr (fun i hi => (u₃ l hl i hi).1),
      fe5_carry _ (by rw [e₂ l hl 4 (by decide)]; have := (u₁ l hl 4 (by decide)).2.2.2; omega)]
    exact fe5_congr fun i hi => by rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.1
  have fM : ∀ l < 4, fe5 (lanes s₅ 0 l) = fe5 (fun i => opV (lanes s 0) l i) * fe5 (fun i => opW (lanes s 0) l i) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₅ l hl i hi).1),
        fe5_mul (fun i hi => by rw [(u₄ l hl i hi).1]; exact b5 l hl i hi)
          (fun i hi => by rw [(u₄ l hl i hi).2]; exact (u₃ l hl i hi).2), ← m₅, fV l hl, fW l hl]
  have f0 : fe5 (fun i => opV (lanes s 0) 0 i) = fe5 (lanes s 0 2) + fe5 (lanes s 0 3) := fe5_add fun _ _ => rfl
  have f1 : fe5 (fun i => opV (lanes s 0) 1 i) = fe5 (lanes s 0 2) - fe5 (lanes s 0 3) :=
    fe5_sub (fun _ _ => rfl) (fun i hi => le_kbv i (hy 3 (by decide) i hi))
  have f2 : fe5 (fun i => opV (lanes s 0) 2 i) = fe5 (lanes s 0 0) := fe5_congr fun _ _ => rfl
  have f3 : fe5 (fun i => opV (lanes s 0) 3 i) = fe5 (lanes s 0 0) - fe5 (lanes s 0 1) :=
    fe5_sub (fun _ _ => rfl) (fun i hi => le_kbv i (hy 1 (by decide) i hi))
  have g0 : fe5 (fun i => opW (lanes s 0) 0 i) = fe5 (lanes s 0 2) + fe5 (lanes s 0 3) := fe5_add fun _ _ => rfl
  have g1 : fe5 (fun i => opW (lanes s 0) 1 i) = fe5 (lanes s 0 2) - fe5 (lanes s 0 3) :=
    fe5_sub (fun _ _ => rfl) (fun i hi => le_kbv i (hy 3 (by decide) i hi))
  have g2 : fe5 (fun i => opW (lanes s 0) 2 i) = fe5 (lanes s 0 1) := fe5_congr fun _ _ => rfl
  have g3 : fe5 (fun i => opW (lanes s 0) 3 i) = Spec.X25519.a24 := fe5_a24
  refine ⟨K, fun l hl i hi => ⟨(u₅ l hl i hi).2, by rw [m₅, (u₄ l hl i hi).1]; exact b5 l hl i hi⟩,
    by rw [fV 2 (by decide), f2], by rw [fV 3 (by decide), f3],
    by rw [fM 0 (by decide), f0, g0], by rw [fM 1 (by decide), f1, g1],
    by rw [fM 2 (by decide), f2, g2], by rw [fM 3 (by decide), f3, g3]⟩

/-- Stage 3 and its product, with stage 2's first operand at `OPV`. -/
theorem part3_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61 ∧ slotv s.mem base OPV l i < 2 ^ 52) :
    WP isa (.block (stage3 ++ mul4 OPG)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61) ∧
      fe5 (lanes s' 0 0) = fe5 (lanes s 0 2) * 1 ∧
      fe5 (lanes s' 0 1) = fe5 (slotv s.mem base OPV 3) * (fe5 (slotv s.mem base OPV 2) + fe5 (lanes s 0 3)) ∧
      fe5 (lanes s' 0 2) = fe5 (lanes s 0 0) * 1 ∧
      fe5 (lanes s' 0 3) = fe5 (lanes s 0 1) * fe5 x1 := by
  have hr := hs.rdi
  simp only [stage3, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s3a_wp hr (scr_ctx hs) hk (fun l hl i hi => (hy l hl i hi).1) (fun l hl i hi => (hy l hl i hi).2))
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2.1)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have e₂ := lanes_keep (s := s₁) (s' := s₂) (r0 := 0) (fun r hr h1 h2 l hl => k₂ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₂.rdi (scr_ctx hs₂) hk₂.c fun l hl i hi => by
      rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.2)
    fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ := scr_of hs₂ (vm_gpr v₃) (vm_wr v₃)
  have e₃ := lanes_keep (s := s₂) (s' := s₃) (r0 := 5) (fun r hr h1 h2 l hl => k₃ r hr (by omega) (by omega) l hl)
    (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (s3b_wp hs₃.rdi (scr_ctx hs₃)) fun s₄ ⟨v₄, o₄, u₄, k₄⟩ => ?_
  have hs₄ := scr_of hs₃ (vm_gpr v₄) (vm_wr v₄)
  have e₄ := lanes_keep (s := s₃) (s' := s₄) (r0 := 5) (fun r hr _ _ l hl => k₄ r hr l hl) (by decide)
  have b5 : ∀ l < 4, ∀ i < 5, lanes s₄ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [e₄ l hl i hi, e₃ l hl i hi]; exact (u₂ l hl i hi).2
  refine WP.mono (mul4_wp (a := OPG) (by decide) (mulS_eq _ _) (mulG_nat) mulG_ok mulG_keep mulG_st
    hs₄.rdi (scr_ctx hs₄) (fun l hl i hi => by rw [u₄ l hl i hi]; exact (u₃ l hl i hi).2) b5)
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  have K : Kept base s s₅ :=
    ((((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans
      ⟨vm_gpr v₄, vm_rd v₄, vm_wr v₄, o₄.mono (by decide) (by decide)⟩).trans (Kept.vm v₅ m₅)
  have fG : ∀ l < 4, fe5 (slotv s₄.mem base OPG l) = fe5 (fun i => opG (lanes s 0) (slotv s.mem base OPV) l i) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => u₄ l hl i hi), fe5_congr (fun i hi => (u₃ l hl i hi).1),
        fe5_carry _ (by rw [e₂ l hl 4 (by decide)]; have := (u₁ l hl 4 (by decide)).2.2.2; omega)]
      exact fe5_congr fun i hi => by rw [e₂ l hl i hi]; exact (u₁ l hl i hi).2.2.1
  have fH : ∀ l < 4, fe5 (lanes s₄ 5 l) = fe5 (fun i => opH x1 (lanes s 0) (slotv s.mem base OPV) l i) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => e₄ l hl i hi), fe5_congr (fun i hi => e₃ l hl i hi),
        fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2.1; omega)]
      exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have fM : ∀ l < 4, fe5 (lanes s₅ 0 l) = fe5 (fun i => opG (lanes s 0) (slotv s.mem base OPV) l i) *
      fe5 (fun i => opH x1 (lanes s 0) (slotv s.mem base OPV) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₅ l hl i hi).1),
      fe5_mul (fun i hi => by rw [u₄ l hl i hi]; exact (u₃ l hl i hi).2) (b5 l hl), fG l hl, fH l hl]
  have h1 : fe5 (fun i => if i = 0 then 1 else 0) = 1 := fe5_one
  refine ⟨K, fun l hl i hi => (u₅ l hl i hi).2, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide)]; exact congrArg₂ _ (fe5_congr fun _ _ => rfl) h1
  · rw [fM 1 (by decide)]
    exact congrArg₂ _ (fe5_congr fun _ _ => rfl) (fe5_add fun _ _ => rfl)
  · rw [fM 2 (by decide)]; exact congrArg₂ _ (fe5_congr fun _ _ => rfl) h1
  · rw [fM 3 (by decide)]; exact congrArg₂ _ (fe5_congr fun _ _ => rfl) (fe5_congr fun _ _ => rfl)

end VG.Proof.X25519.X86_64.Ifma
