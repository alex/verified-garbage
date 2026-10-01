import VerifiedGarbage.Proof.Rc2.Select32

/-! # RC2 word arithmetic in 32-bit registers -/

namespace VG.Proof.Rc2.Word32

theorem maskWord (x : BitVec 32) : x &&& 65535 = (x.setWidth 16).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 16 - 1) = x.toNat % 65536 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem maskWord_lit (x : BitVec 32) : x &&& 65535#32 = (x.setWidth 16).setWidth 32 :=
  maskWord x

theorem rotateWord (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ((x.setWidth 32).rotateRight (32 - n) ||| (x.setWidth 32) >>> (16 - n)) &&& 65535 =
      (x.rotateLeft n).setWidth 32 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega)
  have n16 : n % 16 = n := Nat.mod_eq_of_lt hn'
  rw [n32, n16]
  rw [show 32 - (32 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (16 - n) < 32 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega,
      show j - n < 32 by omega, BitVec.getLsbD_of_ge]

theorem mixWord (x k a b c : BitVec 16) :
    (x.setWidth 32 + k.setWidth 32 +
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))) &&& 65535 =
      (x + k + (a &&& b) + (~~~a &&& c)).setWidth 32 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 32)
  simp [BitVec.setWidth_add, BitVec.setWidth_not, BitVec.add_assoc]

theorem reverseMixWord (x k a b c : BitVec 16) :
    (x.setWidth 32 - k.setWidth 32 -
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))) &&& 65535 =
      (x - k - (a &&& b) - (~~~a &&& c)).setWidth 32 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 32)
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le,
    BitVec.setWidth_not, BitVec.add_assoc, BitVec.neg_add]

theorem rotateLeft_reverse (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    x.rotateLeft (16 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (show 16 - n < 16 by omega),
    show 16 - (16 - n) = n by omega]

theorem subInputsWord (x k c : BitVec 32) :
    (x - k - c) &&& 65535 =
      (x.setWidth 16 - k.setWidth 16 - c.setWidth 16).setWidth 32 := by
  rw [maskWord]
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]

theorem joinBytes_shift (lo hi : VG.Byte) :
    lo.setWidth 32 ||| hi.setWidth 32 <<< 8 =
      (lo.setWidth 16 ||| hi.setWidth 16 <<< 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h : j < 16
  · simp (disch := omega) [h, hj, show j - 8 < 32 by omega, show j - 8 < 16 by omega]
  · simp (disch := omega) [h, hj, BitVec.getLsbD_of_ge]

end VG.Proof.Rc2.Word32
