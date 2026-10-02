import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.X448.Wide.Product

/-! Untrusted: two-word arithmetic for radix-2⁵⁶ X448 coefficients. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi)

/-- The value of a two-word coefficient. -/
def pair (lo hi : BitVec 64) : Nat := lo.toNat + 2 ^ 64 * hi.toNat

/-- A multiply-add below 2¹²⁸ cannot lose a high carry. -/
theorem madd128 (a b lo hi : BitVec 64)
    (h : a.toNat * b.toNat + pair lo hi < 2 ^ 128) :
    pair (addCarry lo (a * b) false)
      (addCarry hi (mulHi a b) (carryOut lo (a * b) false)) =
      a.toNat * b.toNat + pair lo hi := by
  have e0 := addCarry_value lo (a * b) false
  have e1 := addCarry_value hi (mulHi a b) (carryOut lo (a * b) false)
  have em := mul_lo_hi a b
  have hc := Bool.toNat_le (carryOut hi (mulHi a b) (carryOut lo (a * b) false))
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [pair] at h ⊢
  omega

/-- Adding a one-word carry to a coefficient also preserves its value. -/
theorem add128 (lo hi c : BitVec 64) (h : pair lo hi + c.toNat < 2 ^ 128) :
    pair (addCarry lo c false) (addCarry hi 0 (carryOut lo c false)) =
      pair lo hi + c.toNat := by
  have e0 := addCarry_value lo c false
  have e1 := addCarry_value hi 0 (carryOut lo c false)
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl] at e0 e1
  simp only [pair] at h ⊢
  omega

/-- Addition of two coefficients below the two-word capacity. -/
theorem addPair128 (lo hi a b : BitVec 64) (h : pair lo hi + pair a b < 2 ^ 128) :
    pair (addCarry lo a false) (addCarry hi b (carryOut lo a false)) =
      pair lo hi + pair a b := by
  have e0 := addCarry_value lo a false
  have e1 := addCarry_value hi b (carryOut lo a false)
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [pair] at h ⊢
  omega

/-- The low 56-bit digit of a coefficient. -/
theorem low56 (lo hi : BitVec 64) :
    (lo &&& BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = pair lo hi % radix := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = 2 ^ 56 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [pair, radix]
  omega

/-- The upper coefficient bits fit in one word after a 56-bit carry step. -/
theorem high56 (lo hi : BitVec 64) (h : pair lo hi < 2 ^ 119) :
    ((lo >>> 56) + (hi <<< 8)).toNat = pair lo hi / radix := by
  have hh : hi.toNat < 2 ^ 55 := by simp only [pair] at h; omega
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [pair, radix]
  have hl := lo.isLt
  omega

end VG.Proof.X448.Wide
