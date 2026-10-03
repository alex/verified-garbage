import VerifiedGarbage.Proof.Curve448.AArch64.Neon.NFinish
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Math
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Limbs

/-!
# The value and bounds of `mul2`'s results

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Proof.X448.Wide (valN)
open VG.Proof.X448 (toFe toFe_mul)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- The radix-2²⁸ limbs of radix-2⁵⁶ limbs `f`. -/
def l28 (f : Nat → Nat) (k : Nat) : Nat := if k % 2 = 0 then f (k / 2) % 2 ^ 28 else f (k / 2) / 2 ^ 28

theorem psum_l28 (f : Nat → Nat) : psum (l28 f) (2 ^ 28) 16 = (valN f 8 : Int) := by
  have h : ∀ i, (f i : Int) % 268435456 + (f i : Int) / 268435456 * 268435456 = f i := fun i =>
    Int.emod_add_ediv_mul _ _
  simp only [psum, l28, valN, VG.Proof.X448.Wide.radix, Nat.reduceMod, Nat.reduceDiv, ite_true, ite_false,
    one_ne_zero]
  push_cast
  linear_combination h 0 + (72057594037927936 : Int) ^ 1 * h 1 + (72057594037927936 : Int) ^ 2 * h 2 + (72057594037927936 : Int) ^ 3 * h 3 + (72057594037927936 : Int) ^ 4 * h 4 + (72057594037927936 : Int) ^ 5 * h 5 + (72057594037927936 : Int) ^ 6 * h 6 + (72057594037927936 : Int) ^ 7 * h 7

theorem val_out56 (L : Nat → Nat) : (valN (out56 L) 8 : Int) = psum L (2 ^ 28) 16 := by
  simp only [valN, out56, psum, VG.Proof.X448.Wide.radix, w56]
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide,
    show (5 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide,
    show (6 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 1 by decide, show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide, ite_true, ite_false]
  push_cast
  have h0 := Int.emod_add_ediv_mul ((L 0 : Int) + 268435456 * L 1) 72057594037927936
  have h4 := Int.emod_add_ediv_mul ((L 8 : Int) + 268435456 * L 9) 72057594037927936
  linear_combination h0 + (72057594037927936 : Int) ^ 4 * h4

theorem sum_l28 (f : Nat → Nat) : (l28 f 0 : Int) * (2 ^ 28 : Int) ^ 0 + (l28 f 1 : Int) * (2 ^ 28 : Int) ^ 1 + (l28 f 2 : Int) * (2 ^ 28 : Int) ^ 2 + (l28 f 3 : Int) * (2 ^ 28 : Int) ^ 3 + (l28 f 4 : Int) * (2 ^ 28 : Int) ^ 4 + (l28 f 5 : Int) * (2 ^ 28 : Int) ^ 5 + (l28 f 6 : Int) * (2 ^ 28 : Int) ^ 6 + (l28 f 7 : Int) * (2 ^ 28 : Int) ^ 7 + (l28 f 8 : Int) * (2 ^ 28 : Int) ^ 8 + (l28 f 9 : Int) * (2 ^ 28 : Int) ^ 9 + (l28 f 10 : Int) * (2 ^ 28 : Int) ^ 10 + (l28 f 11 : Int) * (2 ^ 28 : Int) ^ 11 + (l28 f 12 : Int) * (2 ^ 28 : Int) ^ 12 + (l28 f 13 : Int) * (2 ^ 28 : Int) ^ 13 + (l28 f 14 : Int) * (2 ^ 28 : Int) ^ 14 + (l28 f 15 : Int) * (2 ^ 28 : Int) ^ 15 = (valN f 8 : Int) := by
  have := psum_l28 f
  simp only [psum, Int.zero_add] at this
  exact this

theorem kara_ex (X : Int) (a b : Nat → Nat) :
    ∃ W : Int, ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7 + (b 8 : Int) * X ^ 8 + (b 9 : Int) * X ^ 9 + (b 10 : Int) * X ^ 10 + (b 11 : Int) * X ^ 11 + (b 12 : Int) * X ^ 12 + (b 13 : Int) * X ^ 13 + (b 14 : Int) * X ^ 14 + (b 15 : Int) * X ^ 15) - (kara a b 0 * X ^ 0 + kara a b 1 * X ^ 1 + kara a b 2 * X ^ 2 + kara a b 3 * X ^ 3 + kara a b 4 * X ^ 4 + kara a b 5 * X ^ 5 + kara a b 6 * X ^ 6 + kara a b 7 * X ^ 7 + kara a b 8 * X ^ 8 + kara a b 9 * X ^ 9 + kara a b 10 * X ^ 10 + kara a b 11 * X ^ 11 + kara a b 12 * X ^ 12 + kara a b 13 * X ^ 13 + kara a b 14 * X ^ 14 + kara a b 15 * X ^ 15) = (X ^ 16 - X ^ 8 - 1) * W := ⟨_, kara_sum X a b⟩

/-- The value of a result of `mul2`: the product of the operands, modulo `p`. -/
theorem mul2_val (fa fb r : Nat → Nat) (hr : ∀ k < 16, (r k : Int) = kara (l28 fa) (l28 fb) k) :
    toFe (valN (out56 (limbs28 r)) 8) = toFe (valN fa 8) * toFe (valN fb 8) := by
  apply toFe_mul
  have hP : ((VG.Spec.X448.P : Nat) : Int) = (2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1 := by
    have h := VG.Proof.X448.full_eq
    simp only [VG.Proof.X448.full, VG.Proof.X448.half, VG.Proof.X448.radix] at h
    have h' : (((2 ^ 28) ^ 16 : Nat) : Int) = (VG.Spec.X448.P : Nat) + (((2 ^ 28) ^ 8 : Nat) : Int) + 1 := by
      rw [h]; push_cast; ring
    push_cast at h'
    linarith
  obtain ⟨W, hW⟩ := kara_ex (2 ^ 28) (l28 fa) (l28 fb)
  rw [sum_l28 fa, sum_l28 fb] at hW
  have e1 := val_out56 (limbs28 r)
  have e2 := limbs28_val r
  simp only [psum] at e1 e2
  rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide), hr 5 (by decide), hr 6 (by decide), hr 7 (by decide), hr 8 (by decide), hr 9 (by decide), hr 10 (by decide), hr 11 (by decide), hr 12 (by decide), hr 13 (by decide), hr 14 (by decide), hr 15 (by decide)] at e2
  generalize (2 ^ 28 : Int) = X at *
  have key : (valN (out56 (limbs28 r)) 8 : Int) =
      (valN fa 8 : Int) * (valN fb 8 : Int) + (X ^ 16 - X ^ 8 - 1) * (-W - C15 r) := by
    linear_combination e1 + e2 - hW
  have : ((valN (out56 (limbs28 r)) 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) =
      ((valN fa 8 * valN fb 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) := by
    rw [key, hP, Int.add_mul_emod_self_left, Nat.cast_mul]
  rw [← Int.natCast_emod, ← Int.natCast_emod] at this
  exact Int.ofNat_inj.mp this

theorem carries_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) :
    cval r 0 7 / 2 ^ 28 < 2 ^ 36 ∧ cval r 8 7 / 2 ^ 28 < 2 ^ 36 :=
  ⟨cin_le (b := 0) (r := r) (fun k hk => hr (0 + k) (by omega)) 8 (by omega),
    cin_le (b := 8) (r := r) (fun k hk => hr (8 + k) (by omega)) 8 (by omega)⟩

theorem limbs28_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {k : Nat} (hk : k < 16) :
    limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) := by
  obtain ⟨c7, c15⟩ := carries_lt hr
  have c7' : C7 r < 2 ^ 36 := c7
  have c15' : C15 r < 2 ^ 36 := c15
  unfold limbs28
  split
  · have := Nat.mod_lt (cval r 0 k) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega
  · have := Nat.mod_lt (cval r 8 (k - 8)) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega

theorem limbs28_bound {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) :
    (∀ i < 8, limbs28 r (2 * i + 1) < 2 ^ 28) ∧ (∀ i < 8, limbs28 r (2 * i) < 2 ^ 40) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := limbs28_lt hr (k := 2 * i + 1) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at this; omega
  · have := limbs28_lt hr (k := 2 * i) (by omega)
    split at this <;> split at this <;> omega

theorem out56_bound {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) : ∀ i < 8, out56 (limbs28 r) i < Mb := by
  have l : ∀ k < 16, limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) :=
    fun k hk => limbs28_lt hr hk
  have l0 := l 0 (by decide); have l1 := l 1 (by decide); have l2 := l 2 (by decide); have l3 := l 3 (by decide)
  have l4 := l 4 (by decide); have l5 := l 5 (by decide); have l6 := l 6 (by decide); have l7 := l 7 (by decide)
  have l8 := l 8 (by decide); have l9 := l 9 (by decide); have l10 := l 10 (by decide)
  have l11 := l 11 (by decide); have l12 := l 12 (by decide); have l13 := l 13 (by decide)
  have l14 := l 14 (by decide); have l15 := l 15 (by decide)
  simp at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
  have d0 : (limbs28 r 0 + 2 ^ 28 * limbs28 r 1) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega)
  have d4 : (limbs28 r 8 + 2 ^ 28 * limbs28 r 9) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega)
  intro i hi
  simp only [Mb, out56, w56]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ite_true, ite_false, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, show (1 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 5 by decide,
      show (3 : Nat) ≠ 4 by decide, show (3 : Nat) ≠ 5 by decide, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
      show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide, show (6 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide, show (7 : Nat) ≠ 1 by decide,
      show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide] <;>
    first
    | exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    | (simp only [Nat.reducePow] at d0 d4 ⊢; omega)

end VG.Proof.Curve448.AArch64.Neon
