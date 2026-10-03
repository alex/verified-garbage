import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs

/-!
# Lanes of the 64-bit lane arithmetic

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64

theorem lane_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VArr.d2.map2 f x y) e = f 64 (vdword x e) (vdword y e) := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact map2_0 f x y
  · exact map2_1 f x y

theorem lane_add (x y : BitVec 128) {e : Nat} (he : e < 2) :
    lane (VArr.d2.map2 (fun _ a b => a + b) x y) e % M64 = (lane x e + lane y e) % M64 := by
  simp only [lane, lane_map2 _ _ _ he, BitVec.toNat_add]
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, h64]
  exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)

theorem lane_sub (x y : BitVec 128) {e : Nat} (he : e < 2) :
    lane (VArr.d2.map2 (fun _ a b => a - b) x y) e % M64 = (lane x e - lane y e) % M64 := by
  simp only [lane, lane_map2 _ _ _ he, BitVec.toNat_sub, M64]
  have := (vdword y e).isLt
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, Int.ofNat_sub (Nat.le_of_lt this), h64,
    Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  omega

theorem lane_ushr (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr sh w a b) y x) e).toNat = (vdword x e).toNat / 2 ^ sh := by
  rw [lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lane_shl (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .shl sh w a b) y x) e).toNat =
      (vdword x e).toNat * 2 ^ sh % 2 ^ 64 := by
  rw [lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lane_and (x m : BitVec 128) {k : Nat} (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ k - 1) {e : Nat} (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ k := by
  rw [vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Curve448.AArch64.Neon
