import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-! Identities for pairs of 64-bit SIMD lanes. -/

namespace VG.AArch64

theorem vdword_ofVDwords_0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    Nat.mul_zero, Nat.zero_add, hi, decide_true, Bool.true_and, ite_true]

theorem vdword_ofVDwords_1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    Nat.mul_one, hi, decide_true, Bool.true_and, show ¬ 64 + i < 64 by omega,
    ite_false, show 64 + i - 64 = i by omega]

theorem vec64_ext {x y : BitVec 128}
    (h0 : vdword x 0 = vdword y 0) (h1 : vdword x 1 = vdword y 1) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 64
  · have := congrArg (fun w : BitVec 64 => w.getLsbD i) h0
    simpa only [vdword, BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and,
      Nat.mul_zero, Nat.zero_add] using this
  · have := congrArg (fun w : BitVec 64 => w.getLsbD (i - 64)) h1
    simpa only [vdword, BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega,
      decide_true, Bool.true_and, Nat.mul_one, show 64 + (i - 64) = i by omega] using this

theorem ext8_pair (a b c d : BitVec 64) :
    (((ofVDwords c d ++ ofVDwords a b) >>> (8 * 8)).extractLsb' 0 128) = ofVDwords b c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, ofVDwords,
    BitVec.getLsbD_append, Nat.zero_add, hi, decide_true, Bool.true_and]
  by_cases h : i < 64
  · simp only [h, show 8 * 8 + i < 128 by omega, show ¬ 8 * 8 + i < 64 by omega,
      ite_true, ite_false, show 8 * 8 + i - 64 = i by omega]
  · simp only [h, show ¬ 8 * 8 + i < 128 by omega, show i - 64 < 64 by omega,
      ite_true, ite_false, show 8 * 8 + i - 128 = i - 64 by omega]

theorem setLane_two (v : BitVec 128) (a b : BitVec 64) :
    setLane (setLane v 64 0 a) 64 1 b = ofVDwords a b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.reduceMul, Nat.sub_zero]
  by_cases h : j < 64 <;> simp (disch := omega) [h, decide_eq_true]

theorem setLane_pair_hi (a b c : BitVec 64) :
    setLane (ofVDwords a b) 64 1 c = ofVDwords a c := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.reduceMul]
  by_cases h : j < 64 <;> simp (disch := omega) [h, decide_eq_true]

end VG.AArch64
