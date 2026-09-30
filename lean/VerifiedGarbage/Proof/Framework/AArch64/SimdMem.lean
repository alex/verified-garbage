import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! AArch64 vector loads, stores, and byte reversal. -/

namespace VG.AArch64

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

theorem getLsbD_readW32 (m : Mem) (a : Addr) (k : Nat) {j : Nat} (hj : j < 32) :
    (m.readW (a + BitVec.ofNat 64 (4 * k)) 32).getLsbD j =
      (m (a + BitVec.ofNat 64 ((32 * k + j) / 8))).getLsbD ((32 * k + j) % 8) := by
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  rw [show 32 / 8 = 4 from rfl, getLsbD_read m 4 _ j (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * k + j / 8 = (32 * k + j) / 8 by omega, show j % 8 = (32 * k + j) % 8 by omega]

theorem read16 (m : Mem) (a : Addr) :
    m.read a 16 = ofVWords (m.readW (a + BitVec.ofNat 64 (4 * 0)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 1)) 32)
      (m.readW (a + BitVec.ofNat 64 (4 * 2)) 32) (m.readW (a + BitVec.ofNat 64 (4 * 3)) 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read m 16 a i (by omega)]
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp only [h0]; rw [getLsbD_readW32 m a 0 h0]; simp
  by_cases h1 : i - 32 < 32
  · simp only [h0, h1]
    rw [getLsbD_readW32 m a 1 h1, show 32 * 1 + (i - 32) = i by omega]; simp
  by_cases h2 : i - 32 - 32 < 32
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 2 h2, show 32 * 2 + (i - 32 - 32) = i by omega]; simp
  · simp only [h0, h1, h2]
    rw [getLsbD_readW32 m a 3 (by omega), show 32 * 3 + (i - 32 - 32 - 32) = i by omega]; simp

theorem toNat_sub_c (d : BitVec 64) (c : Nat) (hc : c < 16) :
    (d - BitVec.ofNat 64 c).toNat = if c ≤ d.toNat then d.toNat - c else 2 ^ 64 + d.toNat - c := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := d.isLt
  split <;> omega

/-- The low word of a 64-bit load. -/
theorem readW64_lo (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add, Mem.readW,
    BitVec.getLsbD_setWidth, show i < 64 by omega]
  rw [getLsbD_read m _ a i (by omega), getLsbD_read m _ a i (by omega)]

/-- The high word of a 64-bit load. -/
theorem readW64_hi (m : Mem) (a : Addr) :
    (m.readW a 64).extractLsb' 32 32 = m.readW (a + BitVec.ofNat 64 4) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW,
    BitVec.getLsbD_setWidth, show 32 + i < 64 by omega]
  rw [getLsbD_read m _ a (32 + i) (by omega), getLsbD_read m _ _ i (by omega), BitVec.add_assoc,
    ← BitVec.ofNat_add, show 4 + i / 8 = (32 + i) / 8 by omega, show i % 8 = (32 + i) % 8 by omega]

theorem getLsbD_ofVWords (w0 w1 w2 w3 : BitVec 32) {i : Nat} (hi : i < 128) :
    (ofVWords w0 w1 w2 w3).getLsbD i =
      if i < 32 then w0.getLsbD i else if i < 64 then w1.getLsbD (i - 32)
      else if i < 96 then w2.getLsbD (i - 64) else w3.getLsbD (i - 96) := by
  simp only [ofVWords, BitVec.getLsbD_append]
  by_cases h0 : i < 32
  · simp [h0]
  by_cases h1 : i < 64
  · simp [h0, h1, show i - 32 < 32 by omega]
  by_cases h2 : i < 96
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by omega, show i - 32 - 32 = i - 64 by omega, show i - 64 < 32 by omega]
  · simp [h0, h1, h2, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 = i - 96 by omega]

theorem write16 (m : Mem) (a : Addr) (w0 w1 w2 w3 : BitVec 32) :
    m.write a 16 (ofVWords w0 w1 w2 w3) =
      (((m.writeW a w0).writeW (a + BitVec.ofNat 64 4) w1).writeW (a + BitVec.ofNat 64 8) w2).writeW
        (a + BitVec.ofNat 64 12) w3 := by
  funext x
  have e : ∀ c : Nat, x - (a + BitVec.ofNat 64 c) = (x - a) - BitVec.ofNat 64 c := fun c => by
    bv_omega
  simp only [Mem.writeW, Mem.write, e, show 32 / 8 = 4 from rfl]
  generalize x - a = d
  rw [toNat_sub_c d 4 (by omega), toNat_sub_c d 8 (by omega), toNat_sub_c d 12 (by omega)]
  have := d.isLt
  have ext : ∀ (k : Nat) (w : BitVec 32), k < 4 → 4 * k ≤ d.toNat → d.toNat < 4 * k + 4 →
      (∀ b < 8, w.getLsbD (8 * (d.toNat - 4 * k) + b) = (ofVWords w0 w1 w2 w3).getLsbD (8 * d.toNat + b)) →
      (ofVWords w0 w1 w2 w3).extractLsb' (8 * d.toNat) 8 =
        (w.setWidth (8 * 4)).extractLsb' (8 * (d.toNat - 4 * k)) 8 := by
    intro k w hk h1 h2 hw
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show 8 * (d.toNat - 4 * k) + b < 8 * 4 by omega]
    exact (hw b hb).symm
  have g := fun (b : Nat) (h : 8 * d.toNat + b < 128) => getLsbD_ofVWords w0 w1 w2 w3 h
  by_cases c3 : 12 ≤ d.toNat
  · by_cases c4 : d.toNat < 16
    · simp only [c3, c4, ite_true, show d.toNat - 12 < 4 by omega]
      refine ext 3 w3 (by omega) c3 (by omega) fun b hb => ?_
      rw [g b (by omega)]
      simp only [show ¬ 8 * d.toNat + b < 96 by omega, show ¬ 8 * d.toNat + b < 64 by omega,
        show ¬ 8 * d.toNat + b < 32 by omega, ite_false, show 8 * (d.toNat - 4 * 3) + b = 8 * d.toNat + b - 96 by omega]
    · simp only [c3, c4, ite_true, ite_false, show ¬ d.toNat - 12 < 4 by omega,
        show ¬ d.toNat - 8 < 4 by omega, show ¬ d.toNat - 4 < 4 by omega, show 8 ≤ d.toNat by omega,
        show 4 ≤ d.toNat by omega, show ¬ d.toNat < 4 by omega]
  by_cases c2 : 8 ≤ d.toNat
  · simp only [c3, c2, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat - 8 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega]
    refine ext 2 w2 (by omega) c2 (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 96 by omega, show ¬ 8 * d.toNat + b < 64 by omega,
      show ¬ 8 * d.toNat + b < 32 by omega, ite_false, ite_true,
      show 8 * (d.toNat - 4 * 2) + b = 8 * d.toNat + b - 64 by omega]
  by_cases c1 : 4 ≤ d.toNat
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat - 4 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by omega]
    refine ext 1 w1 (by omega) c1 (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 64 by omega, show ¬ 8 * d.toNat + b < 32 by omega, ite_false,
      ite_true, show 8 * (d.toNat - 4 * 1) + b = 8 * d.toNat + b - 32 by omega]
  · simp only [c3, c2, c1, ite_true, ite_false, show d.toNat < 16 by omega, show d.toNat < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 12 < 4 by omega, show ¬ 2 ^ 64 + d.toNat - 8 < 4 by omega,
      show ¬ 2 ^ 64 + d.toNat - 4 < 4 by omega]
    refine ext 0 w0 (by omega) (by omega) (by omega) fun b hb => ?_
    rw [g b (by omega)]
    simp only [show 8 * d.toNat + b < 32 by omega, ite_true, show 8 * (d.toNat - 4 * 0) + b = 8 * d.toNat + b by omega]



theorem vword_rev32b (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VRevOp.rev32b.eval x) e = rev32 (vword x e) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, VRevOp.eval]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega)]
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and,
    rev32, VG.getLsbD_cat4]
  by_cases h0 : i < 8
  · simp (disch := omega) only [h0, ite_true, decide_eq_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h1 : i < 16
  · simp (disch := omega) only [h0, h1, ite_false, ite_true, decide_eq_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h2 : i < 24
  · simp (disch := omega) only [h0, h1, h2, ite_false, ite_true, decide_eq_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp (disch := omega) only [h0, h1, h2, ite_false, decide_eq_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

theorem vword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 4) :
    vword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (4 * e)) 32 := by
  rw [read16, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

end VG.AArch64
