import VerifiedGarbage.Proof.TripleDes.Word

namespace VG.Proof.TripleDes.Arm

theorem mask28 (x : BitVec 32) : x &&& 0x0fffffff = (x.setWidth 28).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 28 - 1) = x.toNat % 268435456 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem rotate28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ((x.setWidth 32).rotateRight (32 - n) ^^^ (x.setWidth 32) >>> (28 - n)) &&& 0x0fffffff =
      (x.rotateLeft n).setWidth 32 := by
  rw [mask28]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega)
  have n28 : n % 28 = n := Nat.mod_eq_of_lt (by omega)
  rw [n32, n28]
  rw [show 32 - (32 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (28 - n) < 32 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega,
      show j - n < 32 by omega, BitVec.getLsbD_of_ge]


theorem mask_word (x : BitVec 32) (n : Nat) (hn : 0 < n) (hn32 : n ≤ 32) :
    (x <<< (32 - n)) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 32 - n + j < 32 := by omega
    have hlo : ¬32 - n + j < 32 - n := by omega
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 32 - n + j - (32 - n) = j by omega]
  · have ho : ¬32 - n + j < 32 := by omega
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packed48 (x : BitVec 48) :
    ((x >>> 32).setWidth 16).setWidth 32 ++ x.setWidth 32 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases hlo : i < 32
  · simp only [hlo, ite_true, decide_true, Bool.true_and]
  · simp (disch := omega) only [hlo, ite_false, decide_true, Bool.true_and,
      show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]
    by_cases h48 : i < 48
    · simp only [show i - 32 < 16 by omega, decide_true, Bool.true_and]
    · simp only [show ¬i - 32 < 16 by omega, decide_false, Bool.false_and,
        BitVec.getLsbD_of_ge x i (by omega)]

end VG.Proof.TripleDes.Arm
