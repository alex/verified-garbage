import VerifiedGarbage.Proof.TripleDes.Word

namespace VG.Proof.TripleDes.AArch64

theorem mask_word (x : BitVec 64) (n : Nat) (hn : 0 < n) (hn64 : n ≤ 64) :
    (x <<< (64 - n)) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 64 - n + j < 64 := by omega
    have hlo : ¬64 - n + j < 64 - n := by omega
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 64 - n + j - (64 - n) = j by omega]
  · have ho : ¬64 - n + j < 64 := by omega
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packHalves_shift (l r : BitVec 32) :
    l.setWidth 64 <<< 32 ^^^ r.setWidth 64 = l ++ r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp [h, hj]
  · have hb : j - 32 < 32 := by omega
    simp [h, hj, hb, show j - 32 < 64 by omega,
      BitVec.getLsbD_of_ge r j (by omega)]

end VG.Proof.TripleDes.AArch64
