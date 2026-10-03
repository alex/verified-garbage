import VerifiedGarbage.Proof.Weierstrass.Complete

/-!
# Scalar multiplication as a loop over the scalar's bits

The specification's `mul k P` recurses on `k / 2`; an implementation runs a
fixed number of iterations, one per bit of `k`, most significant first,
doubling an accumulator and adding `P` where the bit is set. After the bits
`t - 1, …, j` the accumulator is `mul (k >>> j) P` (`mul_shiftRight`), and
after all of them it is `mul k P` (`mul_eq_fold`). Multiples of a point of
the curve are on the curve (`onCurve_mul`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- One step of the loop: `(2m)P = mP + mP`, `(2m + 1)P = (mP + mP) + P`
(including `m = 0`, as `O + O = O`). -/
theorem mul_two_mul_add (P : Point C) (m : Nat) (bit : Bool) :
    mul (2 * m + bit.toNat) P =
      if bit then add (add (mul m P) (mul m P)) P else add (mul m P) (mul m P) := by
  by_cases h0 : 2 * m + bit.toNat = 0
  · have hm : m = 0 := by omega
    have hb : bit = false := by cases bit <;> simp_all
    subst hm hb
    rw [mul, ite_eq_left h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mul, ite_eq_left rfl]
    rfl
  · rw [mul, ite_eq_right h0]
    have hd : (2 * m + bit.toNat) / 2 = m := by
      cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hr : (2 * m + bit.toNat) % 2 = bit.toNat := by cases bit <;> simp
    simp only [hd, hr]
    cases bit <;> simp

/-- The step on the scalar's bits: `k >>> j = 2 (k >>> (j + 1)) + bit j`. -/
theorem mul_shiftRight (P : Point C) (k j : Nat) :
    mul (k >>> j) P =
      if k.testBit j then add (add (mul (k >>> (j + 1)) P) (mul (k >>> (j + 1)) P)) P
      else add (mul (k >>> (j + 1)) P) (mul (k >>> (j + 1)) P) := by
  have hk : k >>> j = 2 * (k >>> (j + 1)) + (k.testBit j).toNat := by
    rw [Nat.testBit, Nat.shiftRight_succ, Nat.one_and_eq_mod_two]
    cases h : (k >>> j) % 2 == 1 <;> simp_all <;> omega
  rw [hk, mul_two_mul_add]

/-- The loop's body. -/
def ladderStep (k : Nat) (P R : Point C) (i : Nat) : Point C :=
  if k.testBit i then add (add R R) P else add R R

theorem foldl_ladderStep (P : Point C) (k j : Nat) :
    (List.range j).reverse.foldl (ladderStep k P) (mul (k >>> j) P) = mul k P := by
  induction j with
  | zero => rw [Nat.shiftRight_zero]; rfl
  | succ j ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    rw [ladderStep, ← mul_shiftRight, ih]

/-- Scalar multiplication by a `t`-bit scalar, most significant bit first. -/
theorem mul_eq_fold (P : Point C) {k t : Nat} (hk : k < 2 ^ t) :
    mul k P = (List.range t).reverse.foldl
      (fun R i => if k.testBit i then add (add R R) P else add R R) .infinity := by
  have h0 : k >>> t = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hk
  have := foldl_ladderStep P k t
  rw [h0, mul, ite_eq_left rfl] at this
  exact this.symm

/-- Multiples of a point of the curve are on the curve. -/
theorem onCurve_mul [Fact C.p.Prime] (hp : 2 < C.p) {P : Point C} (hP : onCurve C P = true)
    (k : Nat) : onCurve C (mul k P) = true := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [mul]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0]; rfl
    · rw [ite_eq_right h0]
      have hQ := ih (k / 2) (Nat.div_lt_self (by omega) (by decide))
      have h2 := onCurve_add hp hQ hQ
      dsimp only
      split
      · exact h2
      · exact onCurve_add hp h2 hP

theorem Good.onCurve_mul (hC : Good C) {P : Point C} (hP : onCurve C P = true) (k : Nat) :
    onCurve C (mul k P) = true := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  exact Weierstrass.onCurve_mul hC.two_lt hP k

end VG.Proof.Weierstrass
