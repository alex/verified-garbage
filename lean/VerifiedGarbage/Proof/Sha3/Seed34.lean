import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha3.Arith

namespace VG.Proof.Sha3.Seed34
open VG VG.Spec.Sha3
open VG.Proof.Sha3 (Rep byteOf xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)

/-- The state whose permutation is the absorbed padded seed. -/
def A0 (Bs : List Byte) : Spec.Sha3.State := xorByte (xorByte (Rep 168 Bs) 34 0x1f) 167 0x80

theorem padded_A0 {Bs : List Byte} (h : Bs.length = 34) :
    padded 168 Spec.Sha3.shakeSuffix Bs = keccakF (A0 Bs) := by
  rw [padded, absorb_pad (by decide) (by decide), h]; rfl

theorem byteOf_A0 {Bs : List Byte} (h : Bs.length = 34) {q : Nat} (hq : q < 200) :
    byteOf (A0 Bs) q = if q < 34 then Bs.getD q 0 else if q = 34 then 0x1f else if q = 167 then 0x80 else 0 := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have ha : Spec.Sha3.absorb 168 Bs = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, h]
  have hr : byteOf (Rep 168 Bs) q = Bs.getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, h, show 168 * (34 / 168) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hd : ∀ q, 34 ≤ q → Bs.getD q 0 = 0 := fun q hq' => by
    rw [List.getD, List.getElem?_eq_none (by omega)]; rfl
  rw [A0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr]
  by_cases e1 : q < 34
  · rw [ite_eq_right (show ¬ q = 167 by omega), ite_eq_right (show ¬ q = 34 by omega), ite_eq_left e1]
  · rw [ite_eq_right e1, hd q (by omega)]
    by_cases e2 : q = 34
    · rw [ite_eq_right (show ¬ q = 167 by omega), ite_eq_left e2, ite_eq_left e2]; exact BitVec.zero_xor
    · rw [ite_eq_right e2, ite_eq_right e2]
      by_cases e3 : q = 167
      · rw [ite_eq_left e3, ite_eq_left e3]; exact BitVec.zero_xor
      · rw [ite_eq_right e3, ite_eq_right e3]

/-- Byte `p` of the XOF output of `Bs`, from the states. -/
theorem xofByte_A0 {Bs : List Byte} (h : Bs.length = 34) {n p : Nat} (hp : p < 168) :
    xofByte Bs (168 * n + p) = byteOf (iterF (n + 1) (A0 Bs)) p := by
  rw [xofByte, show (168 * n + p) / 168 = n by omega, show (168 * n + p) % 168 = p by omega, padded_A0 h,
    iterF_keccakF]

end VG.Proof.Sha3.Seed34
