import VerifiedGarbage.Proof.Cmac.Spec

/-!
# CMAC: doubling a 16-byte block as a 128-bit integer

Untrusted: everything here is checked by Lean.

`dbl_eq`: the doubling of §6.1 on 16 bytes (`Spec.Cmac.dbl 16`) is, on the
block as a big-endian 128-bit integer `x` (`Spec.Gcm.ofBytes`), the shift
`x << 1` XORed with `0x87` if the bit shifted out was 1.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-- Bit `j` of byte `i` of a block, as an integer. -/
theorem ofBytes_bit {L : List Byte} (hL : L.length = 16) {i j : Nat} (hi : i < 16) (hj : j < 8) :
    (Spec.Gcm.ofBytes L).getLsbD (8 * (15 - i) + j) = (L.getD i 0).getLsbD j := by
  rw [← Proof.Aes.toBytes_ofBytes hL hi, Proof.Aes.toBytes_getD _ hi, BitVec.getLsbD_extractLsb']
  simp [hj]

/-- The 128-bit doubling. -/
def dbl128 (x : BitVec 128) : BitVec 128 := (x <<< 1) ^^^ (if x.msb then 0x87 else 0)

theorem getD_shiftLeft1 {L : List Byte} (hL : L.length = 16) {k : Nat} (hk : k < 16) :
    (shiftLeft1 L).getD k 0 = (L.getD k 0 <<< 1) ||| (((L.drop 1 ++ [0]).getD k 0 : Byte) >>> 7) := by
  simp [shiftLeft1, List.getD_eq_getElem?_getD, hL, hk]

theorem next_getD {L : List Byte} (hL : L.length = 16) {k : Nat} (hk : k < 15) :
    (L.drop 1 ++ [0]).getD k 0 = L.getD (k + 1) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hL, hk,
    List.getElem?_eq_getElem (show k + 1 < L.length by omega)]

theorem next_getD15 {L : List Byte} (hL : L.length = 16) : (L.drop 1 ++ [0]).getD 15 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, hL]

theorem getD_rb : ∀ k < 16, (rb 16).getD k 0 = if k = 15 then 0x87 else 0 := by decide

theorem testBit_135 : ∀ p < 128, 8 ≤ p → Nat.testBit 135 p = false := by decide

theorem high_0x87 {p : Nat} (hp : 8 ≤ p) : (0x87 : BitVec 128).getLsbD p = false := by
  rw [show (0x87 : BitVec 128) = BitVec.ofNat 128 135 from rfl, BitVec.getLsbD_ofNat]
  by_cases h : p < 128
  · rw [testBit_135 p h hp, Bool.and_false]
  · simp [h]

theorem bit_0x87 : ∀ j < 8, (0x87 : BitVec 128).getLsbD j = (0x87 : Byte).getLsbD j := by decide

theorem dbl_eq {L : List Byte} (hL : L.length = 16) :
    dbl 16 L = Spec.Gcm.toBytes (dbl128 (Spec.Gcm.ofBytes L)) := by
  have hmsb : (Spec.Gcm.ofBytes L).msb = msb1 L := by
    rw [BitVec.msb_eq_getLsbD_last, show 128 - 1 = 8 * (15 - 0) + 7 from rfl,
      ofBytes_bit hL (by decide) (by decide), msb1, BitVec.msb_eq_getLsbD_last]
    cases L with
    | nil => simp at hL
    | cons a _ => rfl
  have hsl : (shiftLeft1 L).length = 16 := by simp [shiftLeft1, hL]
  refine ext16 (by unfold dbl; split <;> simp [length_xor, hsl, rb, zeros]) (toBytes_length _)
    fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', dbl128]
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_xor, hmsb, BitVec.getLsbD_shiftLeft]
  have hdbl : (dbl 16 L).getD k 0 = (shiftLeft1 L).getD k 0 ^^^ (if msb1 L then (rb 16).getD k 0 else 0) := by
    unfold dbl
    split
    · rw [getD_xor (by simp [hsl, rb, zeros]) (by rw [hsl]; exact hk)]
    · simp
  rw [hdbl, getD_shiftLeft1 hL hk, getD_rb k hk]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hj, decide_true, Bool.true_and]
  have hm : ∀ p, 8 ≤ p → (if msb1 L = true then (135 : BitVec 128) else 0).getLsbD p = false := by
    intro p hp; split
    · exact high_0x87 hp
    · simp
  rcases Nat.lt_or_ge k 15 with hk15 | hk15
  · have hm0 : (if msb1 L = true then (if k = 15 then (135 : Byte) else 0) else 0).getLsbD j = false := by
      simp [show k ≠ 15 by omega]
    rw [hm0, hm _ (by omega), Bool.xor_false, Bool.xor_false, next_getD hL hk15]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show 8 * (15 - k) + 0 - 1 = 8 * (15 - (k + 1)) + 7 by omega, ofBytes_bit hL (by omega) (by decide)]
      simp [show ¬ 8 * (15 - k) < 1 by omega, show 8 * (15 - k) < 128 by omega]
    · rw [show 8 * (15 - k) + j - 1 = 8 * (15 - k) + (j - 1) by omega, ofBytes_bit hL hk (by omega),
        BitVec.getLsbD_of_ge _ (7 + j) (by omega)]
      simp [show ¬ j < 1 by omega, show ¬ 8 * (15 - k) + j < 1 by omega, show 8 * (15 - k) + j < 128 by omega]
  · have hk' : k = 15 := by omega
    subst hk'
    rw [next_getD15 hL]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · cases hb : msb1 L
      · simp
      · simp
    · rw [show 8 * (15 - 15) + j - 1 = 8 * (15 - 15) + (j - 1) by omega,
        ofBytes_bit hL (i := 15) (by decide) (by omega)]
      cases hb : msb1 L
      · simp [show ¬ j < 1 by omega, show j < 128 by omega]
      · simp [show ¬ j < 1 by omega, show j < 128 by omega]
        rw [← BitVec.getLsbD_eq_getElem]; exact (bit_0x87 j hj).symm

end VG.Proof.Cmac
