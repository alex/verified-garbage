import VerifiedGarbage.Proof.X448.Wide.SymmetricColumn

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem symmetricColumns_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (fc : ∀ i < 8, (s.gpr (Impl.X448.AArch64.Cached.cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < radix) :
    WP isa (.block ((List.range 16).flatMap (Impl.X448.AArch64.Symmetric.column))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = rows f f 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then rows f f 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (Impl.X448.AArch64.Symmetric.column n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (symmetricColumn_ok (hs.of_keeps tk (by decide)) hn (by
      intro i hi; rw [tk.1 _ (cacheReg_kept hi)]; exact fc i hi) fb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]

    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega
      change pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [outside_coeff um hsep (by simp only [ACC]; omega)]
      change coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega)
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega)], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.X448.Wide
