import VerifiedGarbage.Proof.MlDsa.Arith.Mont
import VerifiedGarbage.Proof.Framework.AArch64.Simd

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

/-- The widening product of two vector words. -/
def product (x z : BitVec 32) : BitVec 64 := x.setWidth 64 * z.setWidth 64

def multiplier (p : BitVec 64) : BitVec 32 := p.extractLsb' 0 32 * BitVec.ofNat 32 montQInv

def redc (p : BitVec 64) : BitVec 32 :=
  (p + (multiplier p).setWidth 64 * BitVec.ofNat 64 q).extractLsb' 32 32

theorem product_nat (x z : BitVec 32) : (product x z).toNat = x.toNat * z.toNat := by
  rw [product, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hx := x.isLt
  have hz := z.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2^64),
    Nat.mod_eq_of_lt (by omega : z.toNat < 2^64)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hx hz) (by decide))

theorem multiplier_nat (p : BitVec 64) : (multiplier p).toNat = montM p.toNat := by
  rw [multiplier, BitVec.toNat_mul, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : montQInv < 2^32)]
  rfl

theorem redc_nat (p : BitVec 64) (hp : p.toNat < q * 2^32) :
    (redc p).toNat = mont p.toNat := by
  have hM := montM_lt p.toNat
  have hR := mont_lt hp
  have hsum := mont_mul p.toNat
  have hq : q = 8380417 := rfl
  have hm : ((multiplier p).setWidth 64 * BitVec.ofNat 64 q).toNat = montM p.toNat * q := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, multiplier_nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : montM p.toNat < 2^64), Nat.mod_eq_of_lt (by decide : q < 2^64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hM (by decide)) (by decide))
  have ha : (p + (multiplier p).setWidth 64 * BitVec.ofNat 64 q).toNat = mont p.toNat * 2^32 := by
    rw [BitVec.toNat_add, hm, ← hsum]
    exact Nat.mod_eq_of_lt (by rw [hq] at hR; omega)
  rw [redc, BitVec.extractLsb'_toNat, ha, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (by decide)]
  exact Nat.mod_eq_of_lt (by rw [hq] at hR; omega)

theorem mont_word_nat (x z : BitVec 32) (hz : z.toNat < q) :
    (redc (product x z)).toNat = mont (x.toNat * z.toNat) := by
  rw [redc_nat _ (by rw [product_nat]; simpa only [Nat.mul_comm] using Nat.mul_lt_mul'' x.isLt hz), product_nat]
end VG.Proof.MlDsa.AArch64.Arith.Neon
