import VerifiedGarbage.Proof.Cmac.Dbl
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Gcm.Bits

/-!
# CMAC: doubling a block in four 32-bit words

The 32-bit targets load a block as four byte-reversed words (`byteRev32`), the
block as a big-endian 128-bit integer `b₀ ++ b₁ ++ b₂ ++ b₃` (`ofBytes_rev4`),
double it a word at a time (`dbl_words4`), and store the words byte-reversed
again (`le4_rev4`).
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

theorem ofBytes_toBytes (x : Spec.Gcm.Block) : Spec.Gcm.ofBytes (Spec.Gcm.toBytes x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < 16 ∧ j < 8 ∧ p = 8 * (15 - i) + j :=
    ⟨15 - p / 8, p % 8, by omega, by omega, by omega⟩
  rw [ofBytes_bit (toBytes_length x) hi hj, Proof.Aes.toBytes_getD _ hi, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem getLsbD_byteRev32 (a : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 a).getLsbD i = a.getLsbD (8 * (3 - i / 8) + i % 8) := by
  simp only [byteRev32]
  rw [VG.getLsbD_cat4]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h
  · simp only [h, ite_true, BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, h.2, ite_true, ite_false, BitVec.getLsbD_extractLsb',
      show i - 8 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i < 16 by omega, h.2, ite_true, ite_false,
      BitVec.getLsbD_extractLsb', show i - 16 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, ite_false,
      BitVec.getLsbD_extractLsb', show i - 24 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega

theorem getD_le4_append4 (a b c d : BitVec 32) {k : Nat} (hk : k < 16) :
    (le4 a ++ le4 b ++ le4 c ++ le4 d).getD k 0 =
      (if k < 4 then a else if k < 8 then b else if k < 12 then c else d).extractLsb' (8 * (k % 4)) 8 := by
  simp only [List.append_assoc, List.getD_eq_getElem?_getD]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
  · rw [List.getElem?_append_left (by rw [length_le4]; omega), ← List.getD_eq_getElem?_getD, getD_le4 _ h]
    simp [h, Nat.mod_eq_of_lt h]
  · rw [List.getElem?_append_right (by rw [length_le4]; omega), length_le4,
      List.getElem?_append_left (by rw [length_le4]; omega), ← List.getD_eq_getElem?_getD,
      getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, h.2, show k % 4 = k - 4 by omega]
  · rw [List.getElem?_append_right (by rw [length_le4]; omega), length_le4,
      List.getElem?_append_right (by rw [length_le4]; omega), length_le4,
      List.getElem?_append_left (by rw [length_le4]; omega), ← List.getD_eq_getElem?_getD,
      getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, show k % 4 = k - 4 - 4 by omega]
  · rw [List.getElem?_append_right (by rw [length_le4]; omega), length_le4,
      List.getElem?_append_right (by rw [length_le4]; omega), length_le4,
      List.getElem?_append_right (by rw [length_le4]; omega), length_le4, ← List.getD_eq_getElem?_getD,
      getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, show k % 4 = k - 4 - 4 - 4 by omega]

/-- Storing the byte-reversed words of `a ++ b ++ c ++ d` stores its bytes,
big-endian. -/
theorem le4_rev4 (a b c d : BitVec 32) :
    le4 (byteRev32 a) ++ le4 (byteRev32 b) ++ le4 (byteRev32 c) ++ le4 (byteRev32 d) =
      Spec.Gcm.toBytes (a ++ b ++ c ++ d) := by
  refine ext16 (by simp [length_le4]) (toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk, getD_le4_append4 _ _ _ _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
  · simp only [h, ite_true, getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, h.2, ite_true, ite_false,
      getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, ite_true, ite_false,
      getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ite_false,
      getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)

theorem mask_eq32 (hi : BitVec 32) :
    ((0 : BitVec 32) - (hi >>> 31)) &&& 0x87 = if hi.msb then 0x87 else 0 := by
  have h : hi >>> 31 = if hi.msb then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
    have := hi.isLt
    by_cases hm : 2 ^ (32 - 1) ≤ hi.toNat
    · rw [decide_eq_true hm]; simp; omega
    · rw [decide_eq_false hm]; simp; omega
  rw [h]
  split <;> decide

theorem bit135_32 : ∀ p < 32, (135 : BitVec 32).getLsbD p = (135 : BitVec 128).getLsbD p := by decide

/-- The words the 32-bit targets store, from the big-endian words `b₀ … b₃`
of a block: the block doubled. -/
def dblW0 (b₀ b₁ : BitVec 32) : BitVec 32 := (b₀ <<< 1) ||| (b₁ >>> 31)
def dblW3 (b₀ b₃ : BitVec 32) : BitVec 32 := (b₃ <<< 1) ^^^ (((0 : BitVec 32) - (b₀ >>> 31)) &&& 0x87)

theorem getLsbD_cat4w (b₀ b₁ b₂ b₃ : BitVec 32) {i : Nat} (hi : i < 128) :
    (b₀ ++ b₁ ++ b₂ ++ b₃).getLsbD i = if i < 32 then b₃.getLsbD i else if i < 64 then b₂.getLsbD (i - 32)
      else if i < 96 then b₁.getLsbD (i - 64) else b₀.getLsbD (i - 96) := by
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | (congr 1; omega) | rfl

theorem getLsbD_shl1 (x : BitVec 32) {i : Nat} (hi : i < 32) :
    (x <<< 1).getLsbD i = (decide (1 ≤ i) && x.getLsbD (i - 1)) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 1 <;> simp [h] <;> omega

theorem getLsbD_shr31 (x : BitVec 32) (i : Nat) : (x >>> 31).getLsbD i = (decide (i = 0) && x.getLsbD 31) := by
  rw [BitVec.getLsbD_ushiftRight]
  by_cases h : i = 0
  · subst h; simp
  · simp only [h, decide_false, Bool.false_and]; exact BitVec.getLsbD_of_ge x _ (by omega)

theorem getLsbD_shl1_128 (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (x <<< 1).getLsbD i = (decide (1 ≤ i) && x.getLsbD (i - 1)) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 1 <;> simp [h] <;> omega

theorem dbl_words4 (b₀ b₁ b₂ b₃ : BitVec 32) :
    dblW0 b₀ b₁ ++ dblW0 b₁ b₂ ++ dblW0 b₂ b₃ ++ dblW3 b₀ b₃ = dbl128 (b₀ ++ b₁ ++ b₂ ++ b₃) := by
  rw [dblW0, dblW0, dblW0, dblW3, mask_eq32, dbl128, BitVec.msb_append, BitVec.msb_append, BitVec.msb_append]
  have h0 : ((32 : Nat) = 0) = False := by simp
  have h64 : ((64 : Nat) = 0) = False := by simp
  have h96 : ((96 : Nat) = 0) = False := by simp
  simp only [h0, h64, h96, ite_false]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [getLsbD_cat4w _ _ _ _ hp]
  rw [BitVec.getLsbD_xor (x := (b₀ ++ b₁ ++ b₂ ++ b₃) <<< 1), getLsbD_shl1_128 _ hp]
  have m87 : (if b₀.msb = true then (135 : BitVec 128) else 0).getLsbD p =
      (decide (p < 32) && (if b₀.msb = true then (135 : BitVec 32) else 0).getLsbD p) := by
    split
    · by_cases h : p < 32
      · simp only [h, decide_true, Bool.true_and]; exact (bit135_32 p h).symm
      · simp only [h, decide_false, Bool.false_and]; exact Proof.Cmac.high_0x87 (by omega)
    · simp
  rw [m87]
  rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 32) ∨ p = 32 ∨ (33 ≤ p ∧ p < 64) ∨ p = 64 ∨ (65 ≤ p ∧ p < 96) ∨
    p = 96 ∨ (97 ≤ p ∧ p < 128)) with h | h | h | h | h | h | h | h
  · subst h
    simp
  · simp only [show p < 32 from h.2, ite_true, BitVec.getLsbD_xor, getLsbD_shl1 _ h.2, show 1 ≤ p from h.1,
      decide_true, Bool.true_and, getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show p - 1 < 32 by omega]
  · subst h
    simp only [show ¬ 32 < 32 by decide, show 32 < 64 by decide, ite_false, ite_true, Nat.sub_self,
      BitVec.getLsbD_or, getLsbD_shl1 _ (by decide : 0 < 32), getLsbD_shr31,
      getLsbD_cat4w _ _ _ _ (by decide : 32 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show p < 64 from h.2, ite_true, ite_false, BitVec.getLsbD_or,
      getLsbD_shl1 _ (show p - 32 < 32 by omega), getLsbD_shr31, show ¬ p - 32 = 0 by omega,
      show 1 ≤ p - 32 by omega, show 1 ≤ p by omega, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.or_false, Bool.xor_false, getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega),
      show ¬ p - 1 < 32 by omega, show p - 1 < 64 by omega]
    congr 1
  · subst h
    simp only [show ¬ 64 < 32 by decide, show ¬ 64 < 64 by decide, show 64 < 96 by decide, ite_false,
      ite_true, Nat.sub_self, BitVec.getLsbD_or, getLsbD_shl1 _ (by decide : 0 < 32), getLsbD_shr31,
      getLsbD_cat4w _ _ _ _ (by decide : 64 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show ¬ p < 64 by omega, show p < 96 from h.2, ite_true, ite_false,
      BitVec.getLsbD_or, getLsbD_shl1 _ (show p - 64 < 32 by omega), getLsbD_shr31,
      show ¬ p - 64 = 0 by omega, show 1 ≤ p - 64 by omega, show 1 ≤ p by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.xor_false,
      getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show ¬ p - 1 < 32 by omega,
      show ¬ p - 1 < 64 by omega, show p - 1 < 96 by omega]
    congr 1
  · subst h
    simp only [show ¬ 96 < 32 by decide, show ¬ 96 < 64 by decide, show ¬ 96 < 96 by decide, ite_false,
      Nat.sub_self, BitVec.getLsbD_or, getLsbD_shl1 _ (by decide : 0 < 32), getLsbD_shr31,
      getLsbD_cat4w _ _ _ _ (by decide : 96 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show ¬ p < 64 by omega, show ¬ p < 96 by omega, ite_false,
      BitVec.getLsbD_or, getLsbD_shl1 _ (show p - 96 < 32 by omega), getLsbD_shr31,
      show ¬ p - 96 = 0 by omega, show 1 ≤ p - 96 by omega, show 1 ≤ p by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.xor_false,
      getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show ¬ p - 1 < 32 by omega,
      show ¬ p - 1 < 64 by omega, show ¬ p - 1 < 96 by omega]
    congr 1

theorem byteRev32_byteRev32 (a : BitVec 32) : byteRev32 (byteRev32 a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_byteRev32 _ hi, getLsbD_byteRev32 _ (by omega)]
  congr 1; omega

/-- The block at `p` as a big-endian integer, from its four byte-reversed words. -/
theorem ofBytes_rev4 (m : Mem) (p : Addr) :
    Spec.Gcm.ofBytes (Spec.Aes.bytesAt m p 16) =
      byteRev32 (m.readW p 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32) ++
        byteRev32 (m.readW (p + BitVec.ofNat 64 8) 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  have h := le4_rev4 (byteRev32 (m.readW p 32)) (byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32))
    (byteRev32 (m.readW (p + BitVec.ofNat 64 8) 32)) (byteRev32 (m.readW (p + BitVec.ofNat 64 12) 32))
  rw [byteRev32_byteRev32, byteRev32_byteRev32, byteRev32_byteRev32, byteRev32_byteRev32] at h
  rw [bytesAt_split4, ← le4_readW, ← le4_readW, ← le4_readW, ← le4_readW, h, ofBytes_toBytes]

end VG.Proof.Cmac
