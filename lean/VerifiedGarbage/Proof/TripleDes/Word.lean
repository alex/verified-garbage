import VerifiedGarbage.Proof.Framework.Bitslice.Table

namespace VG.Proof.TripleDes

theorem mask28 (x : BitVec 64) : x &&& 0x0fffffff = (x.setWidth 28).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 28 - 1) = x.toNat % 268435456 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem rotate28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ((x.setWidth 64).rotateRight (64 - n) ^^^ (x.setWidth 64) >>> (28 - n)) &&& 0x0fffffff =
      (x.rotateLeft n).setWidth 64 := by
  rw [mask28]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n64 : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
  have n28 : n % 28 = n := Nat.mod_eq_of_lt hn'
  rw [n64, n28]
  rw [show 64 - (64 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (28 - n) < 64 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 64 by omega,
      show j - n < 64 by omega, BitVec.getLsbD_of_ge]


theorem packHalves_word (l r : BitVec 32) :
    (l.setWidth 64).rotateRight 32 ^^^ r.setWidth 64 = l ++ r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp (disch := omega) [h, hj, show 32 + j < 64 by omega, BitVec.getLsbD_of_ge]
  · simp (disch := omega) [h, hj, show j - 32 < 64 by omega, BitVec.getLsbD_of_ge]


theorem appended_left (l r : BitVec 32) : ((l ++ r) >>> 32).setWidth 32 = l := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, show ¬32 + j < 32 by omega, ite_false,
    show 32 + j - 32 = j by omega]

theorem appended_right (l r : BitVec 32) : (l ++ r).setWidth 32 = r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, ite_true]

theorem halves_append (x : BitVec 64) : (x >>> 32).setWidth 32 ++ x.setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, decide_true, Bool.true_and, ite_true]
  · simp (disch := omega) [h, show j - 32 < 32 by omega, show 32 + (j - 32) = j by omega]

theorem pack28_word (c d : BitVec 28) :
    ((c.setWidth 64).rotateRight 36 ^^^ d.setWidth 64).setWidth 56 = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_append]
  by_cases h : j < 28
  · simp (disch := omega) [h, hj, show j < 64 by omega, show 36 + j < 64 by omega, BitVec.getLsbD_of_ge]
  · simp (disch := omega) [h, hj, show j < 64 by omega, show j - 28 < 64 by omega, BitVec.getLsbD_of_ge]

theorem split28_upper (x : BitVec 56) :
    x.setWidth 64 >>> 28 = ((x >>> 28).setWidth 28).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 28
  · simp only [h, hj, show 28 + j < 64 by omega, decide_true, Bool.true_and]
  · simp only [h, hj, BitVec.getLsbD_of_ge x (28 + j) (by omega), decide_false, decide_true, Bool.and_false]


end VG.Proof.TripleDes
