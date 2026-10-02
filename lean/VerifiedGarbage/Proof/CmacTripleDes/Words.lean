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

end VG.Proof.CmacTripleDes
