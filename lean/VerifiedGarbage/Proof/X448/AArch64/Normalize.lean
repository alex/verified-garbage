import VerifiedGarbage.Proof.X448.AArch64.Carry

/-!
# X448 on AArch64: modular reduction

Untrusted: everything here is checked by Lean. Three carry passes and two
folds normalize coefficients bounded by 2⁶², preserving their value modulo p.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 16, limbs s.mem base TMP i = f i) (hb : ∀ i < 16, f i < 2 ^ 62) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 16, limbs t.mem base o i = normalized f i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps [.x4, .x6, .x5] s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps [.x4, .x6, .x5] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [normalize, show pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP =
    pass TMP TMP ++ (fold ++ (pass TMP TMP ++ (fold ++ pass o TMP))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp htmp (by decide) (by decide) (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₁ f₁ c₁ (carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok hs₂ htmp htmp (by decide) (by decide) (Or.inl rfl) f₂ (folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₃ f₃ c₃ (carry_bound (folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 128 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp ho8 (by decide) (Or.inr (Or.inl ho')) f₄
    (folded_bound (folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.AArch64
