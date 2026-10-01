import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.X86.PublicKey
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

theorem prune_words (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 32) :
    ((d0.toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * d7.toNat) &&& (2 ^ 254 - 8)) ||| 2 ^ 254 =
      (d0 &&& BitVec.ofNat 32 (2 ^ 32 - 8)).toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * ((d7 &&& BitVec.ofNat 32 (2 ^ 30 - 1)) ||| BitVec.ofNat 32 (2 ^ 30)).toNat := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt; have h5 := d5.isLt; have h6 := d6.isLt; have h7 := d7.isLt
  have c₁ : (2 ^ 32 - 8) % 2 ^ 32 = 2 ^ 32 - 8 := by decide
  have c₂ : (2 ^ 30 - 1) % 2 ^ 32 = 2 ^ 30 - 1 := by decide
  have c₃ : (2 ^ 30) % 2 ^ 32 = 2 ^ 30 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 32 (by omega), and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega)), or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (32 - 3) = 2 ^ 29 from rfl]
  omega

end VG.Proof.Ed25519.X86.PublicKey
