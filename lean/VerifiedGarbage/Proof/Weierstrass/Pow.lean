import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Square-and-multiply from the top bit

The invariant of a loop over the bits of `e` from the top: after the bits
`t - 1 … j`, the accumulator is `b^(e >>> j)`.
-/

namespace VG.Proof.Weierstrass

theorem shiftRight_succ_bit (e j : Nat) :
    e >>> j = 2 * (e >>> (j + 1)) + (if e.testBit j then 1 else 0) := by
  rw [Nat.shiftRight_succ, Nat.testBit, Nat.one_and_eq_mod_two]
  have := Nat.div_add_mod (e >>> j) 2
  rcases Nat.mod_two_eq_zero_or_one (e >>> j) with h | h <;> simp [h] <;> omega

theorem pow_shiftRight {M : Type*} [Monoid M] (b : M) (e j : Nat) :
    b ^ (e >>> j) = (b ^ (e >>> (j + 1))) ^ 2 * (if e.testBit j then b else 1) := by
  rw [← pow_mul, shiftRight_succ_bit e j]
  split <;> simp [pow_add, Nat.mul_comm]

theorem shiftRight_eq_zero {e t : Nat} (h : e < 2 ^ t) : e >>> t = 0 := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt h

end VG.Proof.Weierstrass
