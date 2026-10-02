import VerifiedGarbage.Proof.Framework.X86.Sse

namespace VG.Proof.Sha256.X86.ShaNi
open VG.X86

theorem movd_value (a : BitVec 32) :
    (0 : BitVec 96) ++ a = ofDwords a 0 0 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, getLsbD_ofDwords, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, ite_self]

theorem shift_last_value (a : BitVec 32) :
    XShiftOp.eval .pslldq (ofDwords a 0 0 0) 12 = ofDwords 0 0 0 a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XShiftOp.eval, BitVec.ofNat_eq_ofNat, show min (12#8).toNat 16 * 8 = 96 from rfl,
    BitVec.getLsbD_shiftLeft, getLsbD_ofDwords, BitVec.getLsbD_zero]
  by_cases h : i < 96
  · simp (disch := omega) only [ite_eq_left, ite_self, decide_eq_true, Bool.not_true, Bool.and_false, Bool.false_and]
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false, Bool.not_false, Bool.true_and]
    exact congrArg _ (by omega)

theorem or_last_value (a b c d : BitVec 32) :
    XBinOp.eval .por (ofDwords a b c 0) (ofDwords 0 0 0 d) = ofDwords a b c d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, BitVec.getLsbD_or, getLsbD_ofDwords, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
  by_cases h0 : i < 32
  · simp only [h0, ite_true, Bool.or_false]
  by_cases h1 : i < 64
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  by_cases h2 : i < 96
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  · simp (disch := omega) only [ite_eq_right, Bool.false_or]

end VG.Proof.Sha256.X86.ShaNi
