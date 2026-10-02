import VerifiedGarbage.Proof.X448.Limbs

/-!
# X448: nonnegative limb subtraction

Adding twice the field prime permits every limb subtraction to be performed
without borrowing.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def bias (i : Nat) : Nat := if i = 8 then 2 * radix - 4 else 2 * radix - 2

theorem bias_val : valN bias 16 = 2 * P := by decide +kernel

theorem bias_bound (i : Nat) : radix ≤ bias i ∧ bias i < 2 * radix := by
  unfold bias
  split <;> decide

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + bias i - g i

theorem difference_bound {f g : Nat → Nat} (hf : ∀ i < 16, f i < radix) :
    ∀ i < 16, difference f g i < 2 ^ 62 := by
  intro i hi
  have h1 := hf i hi
  have h2 := (bias_bound i).2
  have hr : 3 * radix < 2 ^ 62 := by decide
  simp only [difference]
  omega

theorem difference_val {f g : Nat → Nat} (hg : ∀ i < 16, g i < radix) :
    valN (difference f g) 16 + valN g 16 = valN f 16 + 2 * P := by
  rw [← valN_add]
  have he : valN (fun i => difference f g i + g i) 16 = valN (fun i => f i + bias i) 16 := by
    apply valN_congr
    intro i hi
    have h1 := hg i hi
    have h2 := (bias_bound i).1
    simp only [difference]
    omega
  rw [he, valN_add, bias_val]

end VG.Proof.X448
