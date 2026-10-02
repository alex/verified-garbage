import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Small
import VerifiedGarbage.Proof.X448.Field

/-!
# The field operations, modulo `p`

Untrusted: everything here is checked by Lean. Reduced elements (`Mb`)
are the outputs of products and the inputs of sums and differences; products
take any limbs below `Ib`, which sums, differences and `a + a24 e` keep.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.Spec.X448
open VG.Impl.Curve448.AArch64.Fast
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub toFe_congr)
open VG.Proof.X448.Wide (radix valN valN_congr valN_add rows reduced reduced_mod rows_val)

theorem Mb_le_Ib : Mb ≤ Ib := by decide

theorem prod_val (f g : Nat → Nat) :
    toFe (valN (prodOut f g) 8) = toFe (valN f 8) * toFe (valN g 8) := by
  apply toFe_mul
  rw [out_mod, reduced_mod, rows_val f g (by decide)]

theorem prod_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Ib) (hg : ∀ i < 8, g i < Ib) :
    ∀ i < 8, prodOut f g i < Mb := (fits_of hf hg).out

theorem twoP_val : valN twoP 8 = 2 * P := by decide +kernel

theorem twoP_le (i : Nat) : Mb ≤ twoP i := by simp only [twoP, Mb]; split <;> omega

theorem twoPW_toNat (i : Nat) : (twoPW i).toNat = twoP i := by
  simp only [twoPW, twoP, K2, K4]; split <;> rfl

/-- `a + 2p - b`, for reduced `b`. -/
def diffN (f g : Nat → Nat) (i : Nat) : Nat := f i + twoP i - g i

theorem diff_val {f g : Nat → Nat} (hg : ∀ i < 8, g i < Mb) :
    toFe (valN (diffN f g) 8) = toFe (valN f 8) - toFe (valN g 8) := by
  apply toFe_sub
  have : valN (diffN f g) 8 + valN g 8 = valN f 8 + 2 * P := by
    rw [← valN_add, ← twoP_val, ← valN_add]
    apply valN_congr
    intro i hi
    have := hg i hi; have := twoP_le i
    simp only [diffN]; omega
  rw [this, Nat.add_mul_mod_self_right]

theorem diff_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) : ∀ i < 8, diffN f g i < Ib := by
  intro i hi
  have := hf i hi
  simp only [diffN, twoP, Mb, Ib] at *
  split <;> omega

theorem diff_word (x y : BitVec 64) (i : Nat) (hx : x.toNat < Mb) (hy : y.toNat < Mb) :
    (x + twoPW i - y).toNat = x.toNat + twoP i - y.toNat := by
  have := twoP_le i
  have h2 : twoP i < 2 ^ 58 := by simp only [twoP]; split <;> omega
  simp only [Mb] at hx hy this
  rw [BitVec.toNat_sub, BitVec.toNat_add, twoPW_toNat]
  have := y.isLt
  simp only [Nat.reducePow] at *
  omega

theorem sum_val (f g : Nat → Nat) :
    toFe (valN (fun i => f i + g i) 8) = toFe (valN f 8) + toFe (valN g 8) := by
  apply toFe_add; rw [valN_add]

theorem sum_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) (hg : ∀ i < 8, g i < Mb) :
    ∀ i < 8, f i + g i < Ib := by
  intro i hi; have := hf i hi; have := hg i hi; simp only [Mb, Ib] at *; omega

theorem sum_word (x y : BitVec 64) (hx : x.toNat < Mb) (hy : y.toNat < Mb) :
    (x + y).toNat = x.toNat + y.toNat := by
  simp only [Mb] at hx hy
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem small_val (f g : Nat → Nat) :
    valN (smallVal f g) 8 + P * sc g 7 = valN f 8 + 39081 * valN g 8 := by
  have hs : ∀ i, sl f g i + radix * sc g i = f i + 39081 * g i := fun i => by
    simp only [sl, sc]; have := Nat.mod_add_div (39081 * g i) radix; omega
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2; have h3 := hs 3
  have h4 := hs 4; have h5 := hs 5; have h6 := hs 6; have h7 := hs 7
  have hp : P = radix ^ 8 - radix ^ 4 - 1 := by decide +kernel
  simp only [valN, smallVal, Nat.reduceAdd, Nat.reduceMod, ite_true, ite_false,
    show ¬ (0 = 4) by decide, show ¬ (1 = 4) by decide, show ¬ (2 = 4) by decide,
    show ¬ (3 = 4) by decide, show ¬ (5 = 4) by decide, show ¬ (6 = 4) by decide,
    show ¬ (7 = 4) by decide, Nat.zero_add, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
  simp only [hp, radix, Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  omega

theorem smallF (f g : Nat → Nat) :
    toFe (valN (smallVal f g) 8) = toFe (valN f 8) + a24 * toFe (valN g 8) := by
  have : toFe (valN (smallVal f g) 8) = toFe (valN f 8 + 39081 * valN g 8) := by
    apply toFe_congr; rw [← small_val, Nat.add_mul_mod_self_left]
  rw [this]
  exact toFe_add (b := 39081 * valN g 8) rfl |>.trans (congrArg _ (toFe_mul rfl))

theorem small_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) (hg : ∀ i < 8, g i < Ib) :
    ∀ i < 8, smallVal f g i < Ib := by
  intro i hi
  have hc : ∀ j < 8, sc g j < 2 ^ 20 := fun j hj => by
    have := hg j hj; simp only [sc, Ib, radix] at *; omega
  have := hf i hi
  have hl := Nat.mod_lt (39081 * g i) (show 0 < radix by decide)
  have := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
  have := hc 7 (by decide)
  simp only [smallVal, sl, Mb, Ib, radix] at *
  split <;> omega

end VG.Proof.Curve448.AArch64.Fast
