import VerifiedGarbage.Proof.Cmac.Dbl
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash

/-!
# AES-CMAC on AArch64: doubling a block in two 64-bit words

`subkeys` loads a block as two byte-reversed words (`rev`), the high and low
halves of the block as a big-endian integer (`Proof.Gcm.AArch64.blockAt_rev`),
doubles the integer a word at a time (`dbl_words`), and stores the halves
byte-reversed again (`le8_rev`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 Proof.Cmac

theorem getD_le8_append (a b : BitVec 64) {k : Nat} (hk : k < 16) :
    (le8 a ++ le8 b).getD k 0 = if k < 8 then a.extractLsb' (8 * k) 8 else b.extractLsb' (8 * (k - 8)) 8 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [length_le8]; omega), ← List.getD_eq_getElem?_getD, getD_le8 _ ‹_›]
  · rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8, ← List.getD_eq_getElem?_getD,
      getD_le8 _ (by omega)]

theorem getLsbD_rev64 (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (8 * (7 - p / 8) + p % 8) :=
  Proof.Gcm.getLsbD_byteRev64 x p hp

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_rev (h l : BitVec 64) :
    le8 (rev64 h) ++ le8 (rev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine ext16 (by simp [length_le8]) (toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', getLsbD_rev64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega, ite_false]
    congr 1; omega
  · rw [getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', getLsbD_rev64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega, ite_true]
    congr 1; omega

theorem mask_eq (hi : BitVec 64) :
    ((0 : BitVec 64) - (hi >>> 63)) &&& 0x87 = if hi.msb then 0x87 else 0 := by
  have h : hi >>> 63 = if hi.msb then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
    have := hi.isLt
    by_cases hm : 2 ^ (64 - 1) ≤ hi.toNat
    · rw [decide_eq_true hm]; simp; omega
    · rw [decide_eq_false hm]; simp; omega
  rw [h]
  split <;> decide

theorem bit135 : ∀ p < 64, (135 : BitVec 64).getLsbD p = (135 : BitVec 128).getLsbD p := by decide

/-- The words `subkeys` stores, from the halves `hi` and `lo` it loads. -/
def dblHi (hi lo : BitVec 64) : BitVec 64 := (hi <<< 1) ||| (lo >>> 63)
def dblLo (hi lo : BitVec 64) : BitVec 64 := (lo <<< 1) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& 0x87)

/-- `subkeys`' doubling of `hi ++ lo`. -/
theorem dbl_words (hi lo : BitVec 64) : dblHi hi lo ++ dblLo hi lo = dbl128 (hi ++ lo) := by
  rw [dblHi, dblLo, mask_eq, dbl128, BitVec.msb_append]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hp, decide_true, Bool.true_and]
  have h0 : ((64 : Nat) = 0) = False := by simp
  simp only [h0, ite_false]
  by_cases h64 : p < 64
  · simp only [h64, ↓reduceIte, show p - 1 < 64 by omega, decide_true, Bool.true_and]
    congr 1
    split
    · exact bit135 p h64
    · simp
  · have hm : (if hi.msb = true then (135 : BitVec 128) else 0).getLsbD p = false := by
      split
      · exact Proof.Cmac.high_0x87 (by omega)
      · simp
    rw [hm, Bool.xor_false]
    simp only [h64, ↓reduceIte, show p - 64 < 64 by omega, decide_true, Bool.true_and]
    rcases Nat.eq_or_lt_of_le (show 64 ≤ p by omega) with rfl | hlt
    · simp
    · rw [BitVec.getLsbD_of_ge lo (63 + (p - 64)) (by omega)]
      simp [show ¬ p - 64 < 1 by omega, show ¬ p < 1 by omega, show ¬ p - 1 < 64 by omega]
      congr 1

end VG.Proof.CmacAes.AArch64
