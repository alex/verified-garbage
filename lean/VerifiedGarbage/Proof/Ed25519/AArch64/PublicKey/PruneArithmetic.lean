import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]; rfl
  rw [e, show (8 : Nat) = 2 ^ 3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow {y k : Nat} (h : y < 2 ^ k) : y ||| 2 ^ k = 2 ^ k + y := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [this, Nat.or_comm]

/-- The pruning of `Spec.Ed25519.prune`, on four 64-bit words. -/
theorem prune_words (d₀ d₁ d₂ d₃ : BitVec 64) :
    ((d₀.toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat + 2 ^ 192 * d₃.toNat) &&& (2 ^ 254 - 8)) |||
        2 ^ 254 =
      (d₀ &&& BitVec.ofNat 64 (2 ^ 64 - 8)).toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat +
        2 ^ 192 * ((d₃ &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)).toNat := by
  have h₀ := d₀.isLt; have h₁ := d₁.isLt; have h₂ := d₂.isLt; have h₃ := d₃.isLt
  have c₁ : (2 ^ 64 - 8) % 2 ^ 64 = 2 ^ 64 - 8 := by decide
  have c₂ : (2 ^ 62 - 1) % 2 ^ 64 = 2 ^ 62 - 1 := by decide
  have c₃ : (2 ^ 62) % 2 ^ 64 = 2 ^ 62 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 64 (by omega), and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega)), or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega

end VG.Proof.Ed25519.AArch64.PublicKey
