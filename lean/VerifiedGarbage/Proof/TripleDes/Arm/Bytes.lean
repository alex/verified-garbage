import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Arm.Permutation
import VerifiedGarbage.Proof.Framework.Arm.Exec

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = rev (m.readW p 32) ++ rev (m.readW (p + 4) 32) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, rev_readW, rev_readW]
  simp only [VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero,
    show (1 : Addr) + 1 = 2 from by decide,
    show (2 : Addr) + 1 = 3 from by decide,
    show (4 : Addr) + 1 = 5 from by decide,
    show (5 : Addr) + 1 = 6 from by decide,
    show (6 : Addr) + 1 = 7 from by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [BitVec.getLsbD_append, ite_eq_left, ite_eq_right,
      Nat.sub_sub] <;> rfl

theorem packed28 (c d : BitVec 28) :
    packedInput 56 28 (d.setWidth 32) (c.setWidth 32) = c ++ d := by
  simp only [packedInput, BitVec.setWidth_setWidth_of_le _ (by decide : 28 ≤ 32),
    BitVec.setWidth_eq]

theorem byteRev64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (byteRev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have cases8 : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases cases8 i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [byteRev64, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
    BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]

theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    blockAt (m.writeW p (byteRev64 x)) p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact byteRev64_byte x i hi

theorem revPair (l r : BitVec 32) : rev r ++ rev l = byteRev64 (l ++ r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [rev, byteRev64, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    congr 2 <;> omega

end VG.Proof.TripleDes.Arm
