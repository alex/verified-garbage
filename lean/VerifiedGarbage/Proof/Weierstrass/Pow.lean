/-!
# Square-and-multiply from the top bit

The invariant of a loop over the bits of `e` from the top: after the bits
`t - 1 … j`, the accumulator is `b^(e >>> j)`, in any semiring of Lean's core
(`Lean.Grind.Semiring`, such as `Fin m`).
-/

namespace VG.Proof.Weierstrass

theorem shiftRight_succ_bit (e j : Nat) :
    e >>> j = 2 * (e >>> (j + 1)) + (if e.testBit j then 1 else 0) := by
  rw [Nat.shiftRight_succ, Nat.testBit, Nat.one_and_eq_mod_two]
  have := Nat.div_add_mod (e >>> j) 2
  rcases Nat.mod_two_eq_zero_or_one (e >>> j) with h | h <;> simp [h] <;> omega

theorem pow_shiftRight {M : Type _} [Lean.Grind.Semiring M] (b : M) (e j : Nat) :
    b ^ (e >>> j) = (b ^ (e >>> (j + 1))) ^ 2 * (if e.testBit j then b else 1) := by
  rw [shiftRight_succ_bit e j, Lean.Grind.Semiring.pow_two, ← Lean.Grind.Semiring.pow_add,
    ← Nat.two_mul]
  split
  · rw [Lean.Grind.Semiring.pow_add, Lean.Grind.Semiring.pow_one]
  · rw [Nat.add_zero, Lean.Grind.Semiring.mul_one]

theorem shiftRight_eq_zero {e t : Nat} (h : e < 2 ^ t) : e >>> t = 0 := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt h

end VG.Proof.Weierstrass
