/-!
# Ed448: pruning a scalar, on 64-bit words

`Spec.Ed448.prune` (clear bits 0–1 and 448–455, set bit 447) on a number given
as seven 64-bit words and a byte: the first word with bits 0–1 cleared, the
seventh with bit 63 set, and no byte above them (`prune_nat`).

This module imports only Lean core: with Mathlib's algebra imported, `2 ^ 448`
can elaborate to a power that unification evaluates, past Lean's threshold
for evaluating exponents.
-/

namespace VG.Proof.Ed448

theorem and_sub4 (x k : Nat) (hk : 2 ≤ k) : x &&& (2 ^ k - 4) = 4 * (x / 4 % 2 ^ (k - 2)) := by
  have e : 2 ^ k - 4 = 2 ^ 2 * (2 ^ (k - 2) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk] <;> rfl
  rw [e, show (4 : Nat) = 2 ^ 2 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 2 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow_mod {q r k : Nat} (hr : r < 2 ^ k) (hq : q ≤ 1) : (2 ^ k * q + r) ||| 2 ^ k = 2 ^ k + r := by
  rw [Nat.two_pow_add_eq_or_of_lt hr]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
  · rw [Nat.mul_zero, Nat.zero_or, Nat.or_comm]
    simpa using (Nat.two_pow_add_eq_or_of_lt hr 1).symm
  · rw [Nat.mul_one, Nat.or_assoc, Nat.or_comm r, ← Nat.or_assoc, Nat.or_self]
    simpa using (Nat.two_pow_add_eq_or_of_lt hr 1).symm

/-- Setting bit `k` of a number below `2^(k+1)`. -/
theorem or_pow_eq {y k : Nat} (h : y < 2 ^ (k + 1)) : y ||| 2 ^ k = 2 ^ k + y % 2 ^ k := by
  have hq : y / 2 ^ k ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr (by
    rw [Nat.pow_succ] at h; omega))
  have := or_two_pow_mod (q := y / 2 ^ k) (Nat.mod_lt y (Nat.two_pow_pos k)) hq
  rwa [Nat.div_add_mod] at this

/-- `Spec.Ed448.prune` on seven 64-bit words and a byte. -/
theorem prune_nat (w0 w1 w2 w3 w4 w5 w6 b : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) (h4 : w4 < 2 ^ 64) (h5 : w5 < 2 ^ 64) (h6 : w6 < 2 ^ 64) :
    ((w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * (w3 + 2 ^ 64 * (w4 + 2 ^ 64 * (w5 + 2 ^ 64 *
      (w6 + 2 ^ 64 * b))))))) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 =
    (w0 &&& (2 ^ 64 - 4)) + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * (w3 + 2 ^ 64 * (w4 + 2 ^ 64 *
      (w5 + 2 ^ 64 * ((w6 ||| 2 ^ 63) + 2 ^ 64 * 0)))))) := by
  rw [and_sub4 _ 448 (by omega), and_sub4 _ 64 (by omega), or_pow_eq (k := 63) (by omega),
    or_pow_eq (k := 447) (by omega)]
  simp only [show 448 - 2 = 446 from rfl, show 64 - 2 = 62 from rfl]
  omega

end VG.Proof.Ed448
