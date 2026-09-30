import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

/-! Loads, stores and byte reversal for pairs of 64-bit lanes. -/

namespace VG.AArch64

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  rw [getLsbD_read m 16 _ (64 * e + i) (by omega), getLsbD_read m 8 _ i (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega,
    show (64 * e + i) % 8 = i % 8 by omega]

theorem read16_dwords (m : Mem) (p : Addr) :
    m.read p 16 = ofVDwords (m.readW p 64) (m.readW (p + BitVec.ofNat 64 8) 64) := by
  apply vec64_ext
  · rw [vdword_read16 _ _ (by decide), vdword_ofVDwords_0]; simp
  · rw [vdword_read16 _ _ (by decide), vdword_ofVDwords_1]

theorem write16_dwords (m : Mem) (p : Addr) (a b : BitVec 64) :
    m.write p 16 (ofVDwords a b) = (m.writeW p a).writeW (p + BitVec.ofNat 64 8) b := by
  funext x
  have e : x - (p + BitVec.ofNat 64 8) = (x - p) - BitVec.ofNat 64 8 := by bv_omega
  simp only [Mem.writeW, Mem.write, e, show 64 / 8 = 8 from rfl]
  generalize x - p = d
  rw [toNat_sub_c d 8 (by decide)]
  have := d.isLt
  by_cases h : d.toNat < 8
  · simp only [show ¬ 8 ≤ d.toNat by omega, ite_false, show ¬ 2 ^ 64 + d.toNat - 8 < 8 by omega,
      h, show d.toNat < 16 by omega, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', ofVDwords, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, show 8 * d.toNat + i < 64 by omega, ite_true]
  · by_cases h16 : d.toNat < 16
    · simp only [show 8 ≤ d.toNat by omega, ite_true, h16, show d.toNat - 8 < 8 by omega]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', ofVDwords, BitVec.getLsbD_append,
        BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
        show ¬ 8 * d.toNat + i < 64 by omega, ite_false,
        show 8 * (d.toNat - 8) + i < 64 by omega,
        show 8 * d.toNat + i - 64 = 8 * (d.toNat - 8) + i by omega]
    · simp only [show 8 ≤ d.toNat by omega, ite_true, h16, show ¬ d.toNat - 8 < 8 by omega,
        h, ite_false]

theorem getLsbD_rev64 (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (rev64 x).getLsbD i = x.getLsbD (8 * (7 - i / 8) + i % 8) := by
  simp only [rev64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
    (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i by omega)
    with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
    exact congrArg x.getLsbD (by omega)

theorem vdword_rev64b (x : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VRevOp.rev64b.eval x) e = rev64 (vdword x e) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, VRevOp.eval]
  rw [show 64 * e + i = 8 * (8 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega), getLsbD_rev64 _ hi]
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega,
    show 8 * (7 - i / 8) + i % 8 < 64 by omega, decide_true, Bool.true_and]
  exact congrArg x.getLsbD (by omega)

end VG.AArch64
