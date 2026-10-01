import VerifiedGarbage.Proof.Rc2.Memory32

/-! # RC2 block memory as pairs of 32-bit words -/

namespace VG.Proof.Rc2.Word32

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

theorem read64_pair (m : Mem) (p : Addr) :
    m.readW p 64 = (m.readW (p + BitVec.ofNat 64 4) 32) ++ (m.readW p 32) := by
  rw [← readW64_hi, ← readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · rename_i h
    simp only [h, decide_true, Bool.true_and, Nat.zero_add]
  · have h : i - 32 < 32 := by omega
    simp only [h, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

theorem write64_pair (m : Mem) (p : Addr) (a b : BitVec 32) :
    m.writeW p (b ++ a) = (m.writeW p a).writeW (p + BitVec.ofNat 64 4) b := by
  funext x
  have e : x - (p + BitVec.ofNat 64 4) = (x - p) - BitVec.ofNat 64 4 := (BitVec.sub_sub _ _ _).symm
  simp only [Mem.writeW, Mem.write, e, show 32 / 8 = 4 from rfl, show (32 + 32) / 8 = 8 from rfl]
  generalize x - p = d
  rw [toNat_sub_c d 4 (by decide)]
  have := d.isLt
  by_cases h : d.toNat < 4
  · simp only [show ¬ 4 ≤ d.toNat by omega, ite_false, show ¬ 2 ^ 64 + d.toNat - 4 < 4 by omega,
      h, show d.toNat < 8 by omega, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, show 8 * d.toNat + i < 32 by omega, ite_true,
      show 8 * d.toNat + i < 8 * ((32 + 32) / 8) by omega]
  · by_cases h16 : d.toNat < 8
    · simp only [show 4 ≤ d.toNat by omega, ite_true, h16, show d.toNat - 4 < 4 by omega]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
        show ¬ 8 * d.toNat + i < 32 by omega, ite_false,
        show 8 * (d.toNat - 4) + i < 32 by omega,
        show 8 * d.toNat + i < 8 * ((32 + 32) / 8) by omega,
        show 8 * d.toNat + i - 32 = 8 * (d.toNat - 4) + i by omega]
    · simp only [show 4 ≤ d.toNat by omega, ite_true, h16, show ¬ d.toNat - 4 < 4 by omega,
        h, ite_false]

theorem pair_xor (a b c d : BitVec 32) :
    ((b ^^^ d) ++ (a ^^^ c)) = (b ++ a) ^^^ (d ++ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  split <;> rfl

end VG.Proof.Rc2.Word32
