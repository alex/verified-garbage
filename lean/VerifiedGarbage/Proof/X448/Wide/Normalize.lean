import VerifiedGarbage.Proof.X448.Wide.Fold

/-! Untrusted: normalize wide coefficients and restore the field-slot interface. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 8, coeff t.mem base o i = encoded (normalized f i) true) ∧
      FieldMem base o s.mem t.mem ∧ Keeps colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps colRegs a b :=
    fun h => h.mono (by decide)
  rw [normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (pass_ok hs htmp (by decide) (Or.inl rfl) false hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₁ f₁ c₁ (carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok hs₂ htmp (by decide) (Or.inl rfl) false f₂ (folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  simp only [encoded, Bool.false_eq_true, ite_false] at f₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok hs₃ f₃ c₃ (carry_bound (folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (pass_ok hs₄ (Nat.le_trans ho (by decide)) ho8
    (Or.inr (Or.inl (Nat.le_trans ho (by decide)))) true f₄
    (folded_bound (folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Wide
