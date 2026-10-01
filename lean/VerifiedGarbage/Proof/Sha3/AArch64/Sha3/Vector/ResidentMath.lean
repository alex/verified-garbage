import VerifiedGarbage.Proof.Sha3.Stream

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.Spec.Sha3 VG.Proof.Sha3

/-- The subtract-and-sign-bit guard admits only complete blocks. Its upper
bound lets the same inexpensive guard terminate the resident loop. -/
theorem enough_iff (n rate : Nat) (hn : n < 2^64) (hr : rate ≤ 168) :
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 rate) >>> 63 = 0) ↔
      rate ≤ n ∧ n < 2^63 + rate := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat,
    show BitVec.toNat (0 : BitVec 64) = 0 from rfl,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : rate < 2^64)]
  omega

/-- A whole rate block is XORed into lanes before the next permutation. -/
theorem xorAt_zero (A : Spec.Sha3.State) (bs : List Byte) :
    xorAt A 0 bs = xorBytes A bs := by
  apply ext_bytes
  intro j hj
  rw [byteOf_xorAt A 0 bs hj, byteOf_xorBytes A bs hj]
  simp only [Nat.zero_le,Nat.zero_add,true_and,Nat.sub_zero]
  by_cases h : j < bs.length
  · simp [h,List.getD]
  · simp [h,List.getD]

/-- An aligned sponge can absorb a complete block entirely in registers. -/
theorem rep_whole {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200)
    (msg bs : List Byte) (ha : msg.length % rate = 0) (hb : bs.length = rate) :
    Rep rate (msg ++ bs) = keccakF (xorBytes (Rep rate msg) bs) := by
  rw [rep_append hr hr' msg bs (by omega) (by omega),ha,hb]
  simp only [Nat.zero_add,ite_true,xorAt_zero]

/-- Consuming a complete rate block retains the aligned position. -/
theorem append_whole_aligned {rate : Nat} (msg bs : List Byte)
    (ha : msg.length % rate = 0) (hb : bs.length = rate) :
    (msg ++ bs).length % rate = 0 := by
  simp only [List.length_append,hb,Nat.add_mod,Nat.mod_self,Nat.add_zero,ha,Nat.zero_mod]

end VG.Proof.Sha3.AArch64.Sha3.Vector
