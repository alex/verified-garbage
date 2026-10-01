import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = bswap64 (m.readW p 64) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, bswap64_readW]
  simp only [VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero]
  rfl


theorem bswap64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (bswap64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases hcases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide) only [bswap64, extractLsb'_append_byte_hi,
      extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
      BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]


theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    blockAt (m.writeW p (bswap64 x)) p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact bswap64_byte x i hi

end VG.Proof.TripleDes.X86_64
