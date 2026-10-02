import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.CmacTripleDes.Bytes

/-!
# TDEA-CMAC: 64-bit words as two 32-bit words

Untrusted: everything here is checked by Lean. For the 32-bit targets: a
key schedule slot's round key from its two little-endian 32-bit words, and
a block (as a big-endian 64-bit integer) from its two.
-/

namespace VG.Proof.CmacTripleDes

open VG

/-- Bit `i` of a little-endian 32-bit word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW32 (m : Mem) (a : Addr) {i : Nat} (hi : i < 32) :
    (m.readW a 32).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega

/-- A slot's round key: the low 16 bits of its high word, and its low word. -/
theorem setWidth48_readW (m : Mem) (a : Addr) :
    (m.readW a 64).setWidth 48 = (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 16 ++ m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega : i < 48), Bool.true_and,
    getLsbD_readW64 _ _ (by omega), BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, getLsbD_readW32 _ _ h]
  · rw [ite_eq_right h, BitVec.getLsbD_setWidth, decide_eq_true (by omega : i - 32 < 16), Bool.true_and,
      getLsbD_readW32 _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 + (i - 32) / 8 = i / 8 by omega, show (i - 32) % 8 = i % 8 by omega]

/-- A little-endian 64-bit word: its high 32-bit word, then its low one. -/
theorem readW64_split (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readW64 _ _ hi, BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, getLsbD_readW32 _ _ h]
  · rw [ite_eq_right h, getLsbD_readW32 _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 + (i - 32) / 8 = i / 8 by omega, show (i - 32) % 8 = i % 8 by omega]

theorem getLsbD_byteRev32 (w : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 w).getLsbD i = w.getLsbD (8 * (3 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [byteRev32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- Two words byte-reversed, as one: the block `y ‖ x` (as a big-endian
integer) is the bytes of `x` then `y`. -/
theorem byteRev32_append (x y : BitVec 32) : byteRev32 x ++ byteRev32 y = byteRev64 (y ++ x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_byteRev64 _ hi, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, getLsbD_byteRev32 _ h, ite_eq_right (by omega)]
    congr 1; omega
  · rw [ite_eq_right h, getLsbD_byteRev32 _ (by omega), ite_eq_left (by omega)]
    congr 1; omega

/-! ## Shifting and doubling `hi:lo` -/

/-- A round key's words: the high one's upper half is zero. -/
theorem append_of_hi (hi lo : BitVec 32) (h : hi >>> 16 = 0) :
    hi ++ lo = (hi.setWidth 16 ++ lo).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  rw [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, decide_eq_true hq, Bool.true_and, BitVec.getLsbD_append]
  by_cases h32 : q < 32
  · rw [ite_eq_left h32, ite_eq_left h32]
  · rw [ite_eq_right h32, ite_eq_right h32, BitVec.getLsbD_setWidth]
    by_cases h48 : q - 32 < 16
    · rw [decide_eq_true h48, Bool.true_and]
    · rw [decide_eq_false h48, Bool.false_and]
      have := congrArg (fun x => x.getLsbD (q - 48)) h
      simp only [BitVec.getLsbD_ushiftRight] at this
      rw [show 16 + (q - 48) = q - 32 by omega] at this
      exact this.trans (by simp)

/-- Shifting the 64-bit integer `hi:lo` left by one, a word at a time. -/
theorem shl_append (hi lo : BitVec 32) : (hi <<< 1 ||| lo >>> 31) ++ lo <<< 1 = (hi ++ lo) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have h64 : i < 64 := by omega
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h0 : i = 0
  · subst h0; simp
  by_cases h32 : i < 32
  · simp [h32, h0, h64, show i - 1 < 32 by omega]
  by_cases h32' : i = 32
  · subst h32'; simp
  · have h1 : ¬ (i - 1 < 32) := by omega
    have h2 : ¬ (31 + (i - 32) < 32) := by omega
    simp [h32, h1, h0, h64, show i - 32 < 32 by omega, show i - 1 - 32 = i - 32 - 1 by omega,
      show ¬ (i - 32 < 1) by omega, BitVec.getLsbD_of_ge lo (31 + (i - 32)) (by omega)]

theorem shr31 (x : BitVec 32) : x >>> 31 = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0; split <;> simp_all
  · rw [BitVec.getLsbD_of_ge x _ (by omega)]
    split <;> simp [BitVec.getLsbD_one, BitVec.getLsbD_zero, h0]

/-- `dbl` doubles `hi:lo` (`dbl64`). -/
theorem dbl_append (hi lo : BitVec 32) :
    (hi <<< 1 ||| lo >>> 31) ++ (lo <<< 1 ^^^ (((0 : BitVec 32) - (hi >>> 31)) &&& (0x1b : BitVec 32))) =
      dbl64 (hi ++ lo) := by
  have hm : (hi ++ lo).msb = hi.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]; simp
  have hc : ((0 : BitVec 32) - (if hi.msb then (1 : BitVec 32) else 0)) &&& (0x1b : BitVec 32) =
      if hi.msb then 0x1b else 0 := by split <;> rfl
  rw [dbl64, hm, ← shl_append, shr31 hi, hc]
  split
  · rw [show (0x1b : BitVec 64) = (0 : BitVec 32) ++ (0x1b : BitVec 32) from rfl, BitVec.xor_append]
    simp
  · rw [show (0 : BitVec 64) = (0 : BitVec 32) ++ (0 : BitVec 32) from rfl, BitVec.xor_append]
    simp

/-- Doubling a word by adding it to itself. -/
theorem add_self (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

end VG.Proof.CmacTripleDes
