import VerifiedGarbage.Proof.Rc2.Select

/-! # RC2 word arithmetic in 64-bit registers -/

namespace VG.Proof.Rc2

theorem maskWord (x : BitVec 64) : x &&& 65535 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 16 - 1) = x.toNat % 65536 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem maskWord_lit (x : BitVec 64) : x &&& 65535#64 = (x.setWidth 16).setWidth 64 :=
  maskWord x

theorem rotateWord (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ((x.setWidth 64).rotateRight (64 - n) ||| (x.setWidth 64) >>> (16 - n)) &&& 65535 =
      (x.rotateLeft n).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n64 : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
  have n16 : n % 16 = n := Nat.mod_eq_of_lt hn'
  rw [n64, n16]
  rw [show 64 - (64 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (16 - n) < 64 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 64 by omega,
      show j - n < 64 by omega, BitVec.getLsbD_of_ge]

theorem mixWord (x k a b c : BitVec 16) :
    (x.setWidth 64 + k.setWidth 64 +
      ((a.setWidth 64 &&& b.setWidth 64) + (~~~(a.setWidth 64) &&& c.setWidth 64))) &&& 65535 =
      (x + k + (a &&& b) + (~~~a &&& c)).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.setWidth_add, BitVec.setWidth_not, BitVec.add_assoc]

theorem reverseMixWord (x k a b c : BitVec 16) :
    (x.setWidth 64 - k.setWidth 64 -
      ((a.setWidth 64 &&& b.setWidth 64) + (~~~(a.setWidth 64) &&& c.setWidth 64))) &&& 65535 =
      (x - k - (a &&& b) - (~~~a &&& c)).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le,
    BitVec.setWidth_not, BitVec.add_assoc, BitVec.neg_add]

theorem rotateLeft_reverse (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    x.rotateLeft (16 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (show 16 - n < 16 by omega),
    show 16 - (16 - n) = n by omega]

theorem subInputsWord (x k c : BitVec 64) :
    (x - k - c) &&& 65535 =
      (x.setWidth 16 - k.setWidth 16 - c.setWidth 16).setWidth 64 := by
  rw [maskWord]
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]

end VG.Proof.Rc2
