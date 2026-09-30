import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-DSA: little-endian words in memory, for every target

Untrusted: everything here is checked by Lean. The `u64` a target loads
from 8 bytes of memory is the little-endian integer of those bytes
(`readW_leNat`), bit by bit (`readW64_getLsbD`).
-/

namespace VG.Proof.MlDsa.Sample

theorem readW64_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 64) :
    (m.readW a 64).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The `u64` at `p`, from the bytes there. -/
theorem readW_leNat (m : Mem) (p : Addr) (L : List Byte) (h : ∀ k < 8, m (p + BitVec.ofNat 64 k) = L.getD k 0) :
    m.readW p 64 = BitVec.ofNat 64 (leNat (L.take 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [readW64_getLsbD m p hk, h _ (by omega), BitVec.getLsbD_ofNat, testBit_leNat, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  simp [hk]

end VG.Proof.MlDsa.Sample
