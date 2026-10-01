import VerifiedGarbage.Proof.Zeroize.Common

namespace VG.Proof.Zeroize
theorem count32 (x : BitVec 32) : x >>> 2 = BitVec.ofNat 32 (x.toNat / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem tail32 (x : BitVec 32) : x &&& 3 = BitVec.ofNat 32 (x.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (3 : BitVec 32).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

end VG.Proof.Zeroize
