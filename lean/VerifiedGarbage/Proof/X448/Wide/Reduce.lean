import VerifiedGarbage.Proof.X448.Wide.CoefficientIO

/-! Untrusted: fold wide product coefficients with 2⁴⁴⁸ = 2²²⁴ + 1. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem reduction_sum (f : Nat → Nat) (k : Nat) :
    f k + ((reduceIndices k).map f).sum = reduced f k := by
  by_cases hk : k < 4
  · simp only [reduceIndices, hk, ite_true, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, reduced, Nat.add_assoc]
  · simp only [reduceIndices, hk, ite_false, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, reduced,
      Nat.add_assoc]

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 8)
    (hb : ∀ i < 16, coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block (reduceCol k)) s fun t =>
      coeff t.mem base TMP k = reduced (coeff s.mem base ACC) k ∧
      Outside base (TMP + 16 * k) 16 s.mem t.mem ∧ Keeps colRegs s t := by
  rw [reduceCol, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadAt_ok hs (o := ACC) (k := k) (by simp only [ACC]; omega) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have ids : ∀ i ∈ reduceIndices k, i < 16 := by
    intro i hi
    by_cases h : k < 4 <;> simp only [reduceIndices, h, ite_true, ite_false,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
      rcases hi with rfl | rfl | rfl <;> omega
  have cap : pair (u.gpr .x4) (u.gpr .x5) +
      ((reduceIndices k).map (coeff u.mem base ACC)).sum < 2 ^ 128 := by
    rw [uv, um, reduction_sum]
    exact Nat.lt_trans (reduced_bound hb k hk) (by decide)
  refine WP.mono (addCoeffs_ok (hs.of_keeps uk (by decide)) (reduceIndices k) ids cap)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (storeAt_ok vs (o := TMP) (k := k) (by simp only [TMP]; omega) (by decide))
    fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [TMP]; omega)
      (by simp only [TMP]; omega), ite_eq_left rfl, vv, uv, um, reduction_sum]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [TMP]; omega)

theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i < 16, coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block ((List.range 8).flatMap reduceCol)) s fun t =>
      (∀ k < 8, coeff t.mem base TMP k = reduced (coeff s.mem base ACC) k) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps colRegs s t := by
  let f := coeff s.mem base ACC
  let inv := fun n (t : State) =>
    (∀ k < n, coeff t.mem base TMP k = reduced f k) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, coeff t.mem base ACC i = f i := by
      intro i hi
      exact outside_coeff tm (by simp only [ACC, TMP]; omega) (by simp only [ACC]; omega)
    have tb : ∀ i < 16, coeff t.mem base ACC i < 2 ^ 116 := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn tb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [uv]
      simp only [reduced]
      rw [av n (by omega), av (n + 8) (by omega)]
      split
      · rename_i hn'
        rw [av (n + 12) (by omega)]
      · rw [av (n + 4) (by omega)]
    · change pair (word u.mem base (TMP + 16 * k)) (word u.mem base (TMP + 16 * k + 8)) = _
      rw [outside_coeff um (by omega) (by simp only [TMP]; omega)]
      exact tf k (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide
