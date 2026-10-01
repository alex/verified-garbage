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

end VG.Proof.TripleDes
