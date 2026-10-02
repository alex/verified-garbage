import VerifiedGarbage.Impl.X448.AArch64.Symmetric
import VerifiedGarbage.Proof.X448.Wide.LoadCached
import VerifiedGarbage.Proof.X448.Wide.SquareProduct
import VerifiedGarbage.Proof.X448.Wide.DoubleTerm
/-! Untrusted: accumulate a square diagonal into an existing coefficient. -/
namespace VG.Proof.X448.Wide
open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
theorem accumSquareBody_ok {s : State} {f : Nat → Nat} {k : Nat} (hk : k < 16)
    (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < radix) {c : Nat} (hc : c < 2 ^ 118)
    (hz : pair (s.gpr .x4) (s.gpr .x5) = c) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.body k)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = c + rows f f 8 k ∧ t.mem = s.mem ∧ Keeps termRegs s t := by
  let inv := fun n (t : State) =>
    pair (t.gpr .x4) (t.gpr .x5) = c + sqrSum f k n ∧ t.mem = s.mem ∧ Keeps termRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then termFrom (cacheReg n) (cacheReg (k - n))
      else termFromDouble (cacheReg n) (cacheReg (k - n)) else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8 ∧ n ≤ k - n
    · rw [ite_eq_left h]
      have hj : k - n < 8 := by omega
      have av : (t.gpr (cacheReg n)).toNat = f n := by rw [tk.1 _ (cacheReg_kept hn), fc n hn]
      have bv : (t.gpr (cacheReg (k - n))).toNat = f (k - n) := by
        rw [tk.1 _ (cacheReg_kept hj), fc (k - n) hj]
      have next := sqrSum_bound fb (n := n + 1) (by omega) hk
      by_cases diag : n = k - n
      · rw [ite_eq_left diag]
        have sum : (t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat +
            pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_left diag] at next
          omega
        refine WP.mono (termFrom_ok t _ _ (cacheReg_ne10 hn) (cacheReg_ne10 hj) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_left diag]
        omega
      · rw [ite_eq_right diag]
        have sum : 2 * ((t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat) +
            pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [sqrSum, ite_eq_left h, ite_eq_right diag] at next
          omega
        refine WP.mono (termFromDouble_ok t _ _ (cacheReg_ne10 hj) (cacheReg_ne11 hj)
          (by rw [av]; exact Nat.lt_trans (fb n hn) (by decide : radix < 2 ^ 63)) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, sqrSum, ite_eq_left h, ite_eq_right diag]
        omega
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [sqrSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  rw [Impl.X448.AArch64.Symmetric.body]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨by simpa only [sqrSum, Nat.add_zero] using hz, rfl, Keeps.refl _ _⟩) fun t ⟨tv, tm, tk⟩ => ?_
  rw [sqrSum_eq f hk] at tv
  exact ⟨tv, tm, tk⟩

end VG.Proof.X448.Wide
