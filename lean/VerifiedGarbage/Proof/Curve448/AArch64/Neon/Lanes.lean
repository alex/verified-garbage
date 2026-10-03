import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-!
# Lanes of the AdvSIMD operations of `Neon.mul2`

Untrusted: everything here is checked by Lean. The 32-bit words and 64-bit
lanes of the results of the operations `mul2` uses, as numbers.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64

theorem toNat_vword (x : BitVec 128) (c : Nat) : (vword x c).toNat = x.toNat / 2 ^ (32 * c) % 2 ^ 32 := by
  simp [vword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_vdword (x : BitVec 128) (e : Nat) : (vdword x e).toNat = x.toNat / 2 ^ (64 * e) % 2 ^ 64 := by
  simp [vdword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- A 64-bit lane is its two words. -/
theorem vdword_words (x : BitVec 128) (e : Nat) :
    (vdword x e).toNat = (vword x (2 * e)).toNat + 2 ^ 32 * (vword x (2 * e + 1)).toNat := by
  rw [toNat_vdword, toNat_vword, toNat_vword, show 32 * (2 * e) = 64 * e by omega,
    show 32 * (2 * e + 1) = 64 * e + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * e) = n
  omega

theorem vword_lo (x : BitVec 128) (e : Nat) : (vword x (2 * e)).toNat = (vdword x e).toNat % 2 ^ 32 := by
  rw [vdword_words]; have := (vword x (2 * e)).isLt; omega

theorem vword_hi (x : BitVec 128) (e : Nat) : (vword x (2 * e + 1)).toNat = (vdword x e).toNat / 2 ^ 32 := by
  rw [vdword_words]; have := (vword x (2 * e)).isLt; omega

/-! ## Permutations -/

theorem trn1_0 (x y : BitVec 128) : vdword (VPermOp.eval .trn1 .d2 x y) 0 = vdword x 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_0]

theorem trn1_1 (x y : BitVec 128) : vdword (VPermOp.eval .trn1 .d2 x y) 1 = vdword y 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_1]

theorem trn2_0 (x y : BitVec 128) : vdword (VPermOp.eval .trn2 .d2 x y) 0 = vdword x 1 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_0]

theorem trn2_1 (x y : BitVec 128) : vdword (VPermOp.eval .trn2 .d2 x y) 1 = vdword y 1 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_1]

theorem uzp1_0 (x y : BitVec 128) : vword (VPermOp.eval .uzp1 .s4 x y) 0 = vword x 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword_ofVWords_0]

theorem uzp1_1 (x y : BitVec 128) : vword (VPermOp.eval .uzp1 .s4 x y) 1 = vword x 2 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword_ofVWords_1]

theorem uzp1_2 (x y : BitVec 128) : vword (VPermOp.eval .uzp1 .s4 x y) 2 = vword y 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword_ofVWords_2]

theorem uzp1_3 (x y : BitVec 128) : vword (VPermOp.eval .uzp1 .s4 x y) 3 = vword y 2 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vword_ofVWords_3]

/-! ## Lanewise operations -/

theorem vdword_and (x y : BitVec 128) (e : Nat) : vdword (x &&& y) e = vdword x e &&& vdword y e := by
  ext i hi
  simp [vdword, BitVec.getElem_extractLsb', BitVec.getElem_and]

theorem vword_and (x y : BitVec 128) (c : Nat) : vword (x &&& y) c = vword x c &&& vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_and]

theorem map2_0 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) :
    vdword (VArr.d2.map2 f x y) 0 = f 64 (vdword x 0) (vdword y 0) := by
  simp only [VArr.map2, vdword_ofVDwords_0]

theorem map2_1 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) :
    vdword (VArr.d2.map2 f x y) 1 = f 64 (vdword x 1) (vdword y 1) := by
  simp only [VArr.map2, vdword_ofVDwords_1]

/-- `ext vd, vn, vm, #8`: the high half of `n`, then the low half of `m`. -/
def extv (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> (8 * 8)).extractLsb' 0 128

theorem ext8_0 (n m : BitVec 128) : vword (extv n m) 0 = vword n 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : 32 * 0 + i < 128 := by omega
  have h2 : 8 * 8 + (0 + (32 * 0 + i)) < 128 := by omega
  simp only [extv, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi,
    h1, h2, decide_true, Bool.true_and, ite_true]
  congr 1
  omega

theorem ext8_1 (n m : BitVec 128) : vword (extv n m) 1 = vword n 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : 32 * 1 + i < 128 := by omega
  have h2 : 8 * 8 + (0 + (32 * 1 + i)) < 128 := by omega
  simp only [extv, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi,
    h1, h2, decide_true, Bool.true_and, ite_true]
  congr 1
  omega

theorem ext8_2 (n m : BitVec 128) : vword (extv n m) 2 = vword m 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extv, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and]
  rw [decide_eq_true (by omega : 32 * 2 + i < 128), Bool.true_and]
  split
  · omega
  · exact congrArg m.getLsbD (by omega)

theorem ext8_3 (n m : BitVec 128) : vword (extv n m) 3 = vword m 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extv, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and]
  rw [decide_eq_true (by omega : 32 * 3 + i < 128), Bool.true_and]
  split
  · omega
  · exact congrArg m.getLsbD (by omega)

theorem umlal_lane (acc n m : BitVec 128) (p e : Nat) :
    (vdword acc e + (vword n (p + e)).setWidth 64 * (vword m (p + e)).setWidth 64).toNat =
      ((vdword acc e).toNat + (vword n (p + e)).toNat * (vword m (p + e)).toNat) % 2 ^ 64 := by
  have h1 := (vword n (p + e)).isLt
  have h2 := (vword m (p + e)).isLt
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : (vword n (p + e)).toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (vword m (p + e)).toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (Nat.le_of_eq (Nat.pow_add 2 32 32).symm))]

theorem umull_lane (n m : BitVec 128) (p e : Nat) :
    ((vword n (p + e)).setWidth 64 * (vword m (p + e)).setWidth 64).toNat =
      (vword n (p + e)).toNat * (vword m (p + e)).toNat := by
  have h1 := (vword n (p + e)).isLt
  have h2 := (vword m (p + e)).isLt
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : (vword n (p + e)).toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (vword m (p + e)).toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (Nat.le_of_eq (Nat.pow_add 2 32 32).symm))]

/-! ## Memory -/

theorem write16_word (m : Mem) (a : Addr) (v : BitVec 128) {c : Nat} (hc : c < 4) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (4 * c)) 32 = vword v c := by
  rw [← vword_read16 _ _ hc]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_read _ 16 a i hi]
  simp only [Mem.write]
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i / 8 < 2 ^ 64),
    ite_eq_left_iff.mpr fun h => absurd (by omega : i / 8 < 16) h, BitVec.getLsbD_extractLsb']
  simp only [show i % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1
  omega

end VG.Proof.Curve448.AArch64.Neon
