import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# TDEA-CMAC: blocks as bytes and as 64-bit integers

Untrusted: everything here is checked by Lean.

CMAC works on lists of bytes; TDEA on 64-bit integers, big-endian
(`decodeBlock`, `encodeBlock`); the implementations load and store
little-endian words (`le8`), and reverse their bytes (`byteRev64`). So the
cipher of the bytes of a word is the bytes of a word (`tdesWith_le8`), and
so is the doubling of §6.1 (`dbl_le8`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes Proof.Cmac Spec.Cmac

theorem getLsbD_byteRev64 (w : BitVec 64) {i : Nat} (hi : i < 64) :
    (byteRev64 w).getLsbD i = w.getLsbD (8 * (7 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [byteRev64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem getLsbD_foldl_bytes (L : List Byte) (init : BitVec 64) {i : Nat} (hi : i < 64) :
    (L.foldl (fun (out : BitVec 64) (byte : Byte) => (out <<< 8) ||| byte.zeroExtend 64) init).getLsbD i =
      if i < 8 * L.length then (L.getD (L.length - 1 - i / 8) 0).getLsbD (i % 8)
      else init.getLsbD (i - 8 * L.length) := by
  induction L generalizing init with
  | nil => simp
  | cons b L ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h₁ : i < 8 * L.length
    · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      rw [show L.length + 1 - 1 - i / 8 = (L.length - 1 - i / 8) + 1 by omega]
      simp
    · rw [ite_eq_right h₁]
      by_cases h₂ : i < 8 * (L.length + 1)
      · rw [ite_eq_left h₂, show L.length + 1 - 1 - i / 8 = 0 by omega, decide_eq_true (by omega : i - 8 * L.length < 64),
          decide_eq_true (by omega : i - 8 * L.length < 8), show i - 8 * L.length = i % 8 by omega]
        simp
      · rw [ite_eq_right h₂, decide_eq_true (by omega : i - 8 * L.length < 64),
          decide_eq_false (by omega : ¬ i - 8 * L.length < 8), BitVec.getLsbD_of_ge b _ (by omega),
          show i - 8 * L.length - 8 = i - 8 * (L.length + 1) by omega]
        simp

theorem getLsbD_decode (v : Block) {i : Nat} (hi : i < 64) :
    (decodeBlock v).getLsbD i = (v.toList.getD (7 - i / 8) 0).getLsbD (i % 8) := by
  rw [decodeBlock, getLsbD_foldl_bytes _ _ hi, Vector.length_toList, ite_eq_left (by omega)]

theorem getD_le8_bit (w : BitVec 64) {k j : Nat} (hk : k < 8) (hj : j < 8) :
    ((le8 w).getD k 0).getLsbD j = w.getLsbD (8 * k + j) := by
  rw [getD_le8 _ hk, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]

theorem decode_le8 (w : BitVec 64) : decodeBlock (Vector.ofFn fun i => (le8 w).getD i 0) = byteRev64 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_decode _ hi, getLsbD_byteRev64 _ hi, Vector.toList_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp only [show 7 - i / 8 < 8 by omega, dite_true, Option.getD_some]
  rw [getD_le8_bit _ (by omega) (Nat.mod_lt _ (by decide))]

theorem encode_le8 (y : BitVec 64) : (encodeBlock y).toList = le8 (byteRev64 y) := by
  apply List.ext_getElem (by simp [le8])
  intro k h₁ h₂
  have hk : k < 8 := by simpa using h₁
  simp only [le8, List.getElem_map, List.getElem_range, encodeBlock, Vector.toList_ofFn, List.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, getLsbD_byteRev64 _ (by omega),
    BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
  congr 1; omega

theorem tdesWith_le8 (S : Schedule) (w : BitVec 64) :
    Spec.Cmac.tdesWith S (le8 w) = le8 (byteRev64 (tdes S (byteRev64 w))) := by
  rw [Spec.Cmac.tdesWith, encryptBlock, decode_le8, encode_le8]
  rfl

/-- Bit `j` of byte `k` of a block as a big-endian integer. -/
theorem le8_rev_bit (y : BitVec 64) {k j : Nat} (hk : k < 8) (hj : j < 8) :
    ((le8 (byteRev64 y)).getD k 0).getLsbD j = y.getLsbD (8 * (7 - k) + j) := by
  rw [getD_le8_bit _ hk hj, getLsbD_byteRev64 _ (by omega)]
  congr 1; omega

/-- The 64-bit doubling. -/
def dbl64 (y : BitVec 64) : BitVec 64 := (y <<< 1) ^^^ (if y.msb then 0x1b else 0)

theorem ext8 {x y : List Byte} (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ k < 8, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem (by rw [hx, hy])
  intro k h₁ h₂
  have := h k (by omega)
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem getD_rb8 : ∀ k < 8, (rb 8).getD k 0 = if k = 7 then 0x1b else 0 := by decide

theorem high_0x1b {p : Nat} (hp : 8 ≤ p) : (0x1b : BitVec 64).getLsbD p = false := by
  rw [show (0x1b : BitVec 64) = BitVec.ofNat 64 27 from rfl, BitVec.getLsbD_ofNat]
  have : Nat.testBit 27 p = false := by
    apply Nat.testBit_lt_two_pow
    calc 27 < 2 ^ 8 := by decide
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  rw [this, Bool.and_false]

theorem bit_0x1b : ∀ j < 8, (0x1b : BitVec 64).getLsbD j = (0x1b : Byte).getLsbD j := by decide

theorem dbl_le8 (y : BitVec 64) : dbl 8 (le8 (byteRev64 y)) = le8 (byteRev64 (dbl64 y)) := by
  have hL : (le8 (byteRev64 y)).length = 8 := length_le8 _
  have hmsb : msb1 (le8 (byteRev64 y)) = y.msb := by
    have h := le8_rev_bit y (k := 0) (j := 7) (by decide) (by decide)
    rw [BitVec.msb_eq_getLsbD_last, show 64 - 1 = 8 * (7 - 0) + 7 from rfl, ← h, msb1,
      BitVec.msb_eq_getLsbD_last]
    rfl
  have hsl : (shiftLeft1 (le8 (byteRev64 y))).length = 8 := by simp [shiftLeft1, hL]
  refine ext8 (by unfold dbl; split <;> simp [length_xor, hsl, rb, zeros]) (length_le8 _) fun k hk => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [le8_rev_bit _ hk hj, dbl64]
  have hdbl : (dbl 8 (le8 (byteRev64 y))).getD k 0 = (shiftLeft1 (le8 (byteRev64 y))).getD k 0 ^^^
      (if msb1 (le8 (byteRev64 y)) then (rb 8).getD k 0 else 0) := by
    unfold dbl
    split
    · rw [getD_xor (by simp [hsl, rb, zeros]) (by rw [hsl]; exact hk)]
    · simp
  have hs : (shiftLeft1 (le8 (byteRev64 y))).getD k 0 =
      ((le8 (byteRev64 y)).getD k 0 <<< 1) ||| ((((le8 (byteRev64 y)).drop 1 ++ [0]).getD k 0 : Byte) >>> 7) := by
    simp [shiftLeft1, List.getD_eq_getElem?_getD, hL, hk]
  rw [hdbl, hs, getD_rb8 k hk, hmsb]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hj, decide_true, Bool.true_and]
  have hm : ∀ p, 8 ≤ p → (if y.msb = true then (0x1b : BitVec 64) else 0).getLsbD p = false := by
    intro p hp; split
    · exact high_0x1b hp
    · simp
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · have hm0 : (if y.msb = true then (if k = 7 then (0x1b : Byte) else 0) else 0).getLsbD j = false := by
      simp [show k ≠ 7 by omega]
    have hnext : ((le8 (byteRev64 y)).drop 1 ++ [0]).getD k 0 = (le8 (byteRev64 y)).getD (k + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hL, hk7,
        List.getElem?_eq_getElem (show k + 1 < (le8 (byteRev64 y)).length by omega)]
    rw [hm0, hm _ (by omega), Bool.xor_false, Bool.xor_false, hnext]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show 8 * (7 - k) + 0 - 1 = 8 * (7 - (k + 1)) + 7 by omega, ← le8_rev_bit y (by omega) (by decide)]
      simp [show ¬ 8 * (7 - k) < 1 by omega, show 8 * (7 - k) < 64 by omega]
    · rw [show 8 * (7 - k) + j - 1 = 8 * (7 - k) + (j - 1) by omega, ← le8_rev_bit y hk (by omega),
        BitVec.getLsbD_of_ge _ (7 + j) (by omega)]
      simp [show ¬ j < 1 by omega, show ¬ 8 * (7 - k) + j < 1 by omega, show 8 * (7 - k) + j < 64 by omega]
  · have hk' : k = 7 := by omega
    subst hk'
    have hnext : ((le8 (byteRev64 y)).drop 1 ++ [0]).getD 7 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hL]
    rw [hnext]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · cases hb : y.msb
      · simp
      · simp
    · rw [show 8 * (7 - 7) + j - 1 = 8 * (7 - 7) + (j - 1) by omega, ← le8_rev_bit y (k := 7) (by decide) (by omega)]
      cases hb : y.msb
      · simp [show ¬ j < 1 by omega, show j < 64 by omega]
      · simp [show ¬ j < 1 by omega, show j < 64 by omega]
        exact (bit_0x1b j hj).symm

end VG.Proof.CmacTripleDes
