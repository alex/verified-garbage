import VerifiedGarbage.Spec.Argon2

/-! # Binary division used by Argon2's index arithmetic -/

namespace VG.Proof.Argon2

/-- Doubling a remainder and inserting one bit needs at most one subtraction. -/
theorem divide_step {n d q r bit : Nat}
    (hn : n = q * d + r) (hr : r < d) (hb : bit ≤ 1) :
    let v := 2 * r + bit
    let take := if v < d then 0 else 1
    let rem := if v < d then v else v - d
    2 * n + bit = (2 * q + take) * d + rem ∧ rem < d := by
  dsimp only
  split
  · next h =>
    simp only [Nat.add_zero]
    constructor
    · rw [hn, Nat.mul_add, Nat.mul_assoc]
      omega
    · exact h
  · next h =>
    constructor
    · rw [hn, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
    · omega

/-- The loop invariant uniquely determines both outputs of division. -/
theorem divide_result {n d q r : Nat} (hd : 0 < d)
    (hn : n = q * d + r) (hr : r < d) : q = n / d ∧ r = n % d := by
  rw [hn, Nat.add_comm (q * d), Nat.add_mul_div_right _ _ hd,
    Nat.div_eq_of_lt hr, Nat.zero_add, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hr]
  exact ⟨rfl, rfl⟩

end VG.Proof.Argon2
