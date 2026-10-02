import VerifiedGarbage.Proof.X448.Arm.Carry

/-!
# X448 on ARMv7: modular reduction
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 112 ≤ ACC) {f : Nat → Nat}
    (hf : ∀ i < 28, limbs s.mem base TMP i = f i) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = normalized f i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps [.r3, .r5, .r4] s t := by
  have htmp : TMP + 112 ≤ 4096 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 112 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.r3] a b → Keeps [.r3, .r5, .r4] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [normalize, show pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP =
    pass TMP TMP ++ (fold ++ (pass TMP TMP ++ (fold ++ pass o TMP))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp htmp (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₁ f₁ c₁ (carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok hs₂ htmp htmp (Or.inl rfl) f₂ (folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₃ f₃ c₃ (carry_bound (folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 112 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp (Or.inr (Or.inl ho')) f₄
    (folded_bound (folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Arm
