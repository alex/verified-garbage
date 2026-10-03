import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-!
# Blocks as little-endian words

A block's little-endian word holds bit `i` of the block (big-endian, as
`decodeBlock` reads it) at bit `i ^^^ 56`: the byte order is reversed.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

theorem xor56_lt {p : Nat} (hp : p < 64) : p ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hp (by decide)

theorem xor56_xor56 (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem getLsbD_rev64' (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (p ^^^ 56) := by
  rw [getLsbD_rev64 _ hp, xor56_eq p hp]

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (decodeBlock (blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.AArch64.decodeBlock_readW, getLsbD_rev64' _ (xor56_lt hj), xor56_xor56]

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    blockAt m p = encodeBlock x := by
  have hw : m.readW p 64 = rev64 x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [h j hj, getLsbD_rev64' _ hj]
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m p (n := 8) hi]
  have e : (m.read p 8) = m.readW p 64 := by simp only [Mem.readW]; rfl
  rw [e, hw]
  exact VG.Proof.TripleDes.AArch64.rev64_byte x i hi

end VG.Proof.TripleDes.AArch64.BitslicedNeon
