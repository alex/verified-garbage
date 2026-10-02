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

theorem shr32 (x : BitVec 32) (k : Nat) : x >>> k = BitVec.ofNat 32 (x.toNat / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem and7_32 (a : Nat) : BitVec.ofNat 32 a &&& 7 = BitVec.ofNat 32 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

/-- Eight zero words of 32 bits after a zero prefix. -/
theorem prefix_writeW8 {m : Mem} {p : Addr} {i : Nat} (h : Prefix m p i) (hn : i + 32 < 2 ^ 64) :
    Prefix ((((((((m.writeW (p + BitVec.ofNat 64 i) (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 (i + 4))
      (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 (i + 8)) (0 : BitVec 32)).writeW
      (p + BitVec.ofNat 64 (i + 12)) (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 (i + 16)) (0 : BitVec 32)).writeW
      (p + BitVec.ofNat 64 (i + 20)) (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 (i + 24)) (0 : BitVec 32)).writeW
      (p + BitVec.ofNat 64 (i + 28)) (0 : BitVec 32)) p (i + 32) := by
  have h1 := prefix_writeW (w := 32) h (by omega)
  have h2 := prefix_writeW (w := 32) h1 (by omega)
  have h3 := prefix_writeW (w := 32) h2 (by omega)
  have h4 := prefix_writeW (w := 32) h3 (by omega)
  have h5 := prefix_writeW (w := 32) h4 (by omega)
  have h6 := prefix_writeW (w := 32) h5 (by omega)
  have h7 := prefix_writeW (w := 32) h6 (by omega)
  have h8 := prefix_writeW (w := 32) h7 (by omega)
  exact h8

end VG.Proof.Zeroize
