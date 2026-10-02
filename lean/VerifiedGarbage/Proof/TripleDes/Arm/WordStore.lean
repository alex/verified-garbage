import VerifiedGarbage.Proof.Framework.Mem

namespace VG.Proof.TripleDes.Arm
open VG

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem readW_pair (m : Mem) (p : Addr) :
    m.readW (p + 4) 32 ++ m.readW p 32 = m.readW p 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases hlo : i < 32
  · rw [ite_eq_left hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hlo, hi, decide_true, Bool.true_and]
    rw [getLsbD_read m 4 p i (by omega), getLsbD_read m 8 p i (by omega)]
  · rw [ite_eq_right hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hi,
      show i - 32 < 32 by omega, decide_true, Bool.true_and]
    rw [getLsbD_read m 4 (p + 4) (i - 32) (by omega), getLsbD_read m 8 p i (by omega)]
    have ha : 4 + (i - 32) / 8 = i / 8 := by omega
    have hb : (i - 32) % 8 = i % 8 := by omega
    rw [hb]
    exact congrArg (fun q => (m q).getLsbD (i % 8))
      ((VG.Offset.add_ofNat_add_ofNat p 4 ((i - 32) / 8)).trans
        (congrArg (fun j => p + BitVec.ofNat 64 j) ha))

theorem writeW_pair (m : Mem) (p : Addr) (lo hi : BitVec 32) :
    (m.writeW p lo).writeW (p + 4) hi = m.writeW p (hi ++ lo) := by
  funext a
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  by_cases hhi : (a - (p + 4)).toNat < 4
  · have he : (a - p).toNat = (a - (p + 4)).toNat + 4 := by bv_omega
    have hb : (a - p).toNat < 8 := by omega
    rw [ite_eq_left hhi, ite_eq_left hb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega) only [ite_eq_right, he]
    apply congrArg (fun b => decide (i < 8) && b)
    apply congrArg hi.getLsbD
    omega
  · rw [ite_eq_right hhi]
    by_cases hlo : (a - p).toNat < 4
    · have hb : (a - p).toNat < 8 := by omega
      rw [ite_eq_left hlo, ite_eq_left hb]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi'
      simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        ite_eq_left]
    · have hb : ¬ (a - p).toNat < 8 := by bv_omega
      rw [ite_eq_right hlo, ite_eq_right hb]

end VG.Proof.TripleDes.Arm
