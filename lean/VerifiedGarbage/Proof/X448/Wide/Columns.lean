import VerifiedGarbage.Proof.X448.Wide.Column

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : a + 64 ≤ ACC ∨ ACC + 256 ≤ a) (hb : b + 64 ≤ ACC ∨ ACC + 256 ≤ b)
    (ha' : a + 64 ≤ 8192) (hb' : b + 64 ≤ 8192) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < radix)
    (fb : ∀ i < 8, limbs s.mem base b i < radix) :
    WP isa (.block ((List.range 16).flatMap (column a b))) s fun t =>
      (∀ k < 16, coeff t.mem base ACC k = rows (limbs s.mem base a) (limbs s.mem base b) 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    (∀ k < 16, coeff t.mem base ACC k = if k < n then rows f g 8 k else coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (column a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 8, limbs t.mem base a i = f i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    have bv : ∀ i < 8, limbs t.mem base b i = g i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    refine WP.mono (column_ok (hs.of_keeps tk (by decide)) ha' hb' ha8 hb8 hn
      (by intro i hi; rw [av i hi]; exact fa i hi)
      (by intro i hi; rw [bv i hi]; exact fb i hi)) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]
      exact rows_congr av bv (by decide) n
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
