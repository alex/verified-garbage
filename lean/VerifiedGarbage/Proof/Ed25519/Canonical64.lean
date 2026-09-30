import VerifiedGarbage.Proof.Ed25519.Field64

/-! Target-independent canonicalization of four field limbs. -/
namespace VG.Proof.Ed25519.Word64
open VG.Spec.X25519 (P)

def mask (sw : Bool) : Word := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : Word) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_sel' (sw : Bool) (a b : Word) :
    a ^^^ ((b ^^^ a) &&& mask sw) = if sw then b else a := by
  rw [BitVec.xor_comm b a]
  exact (xor_sel sw a b).1

theorem and_low63 (x : Word) : (x &&& 0x7fffffffffffffff).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_and, show (0x7fffffffffffffff : Word).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem fold_top (a0 a1 a2 a3 a3' m : Word) (hm : m.toNat = 19 * (a3.toNat / 2 ^ 63))
    (hl : a3'.toNat = a3.toNat % 2 ^ 63) :
    let c0 := carryOut a0 m false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let v := val4 (addCarry a0 m false) (addCarry a1 0 c0)
      (addCarry a2 0 c1) (addCarry a3' 0 c2)
    v % P = val4 a0 a1 a2 a3 % P ∧ v < 2 ^ 255 + 19 := by
  intro c0 c1 c2 v
  have e := add4_value a0 a1 a2 a3' m 0 0 0 false
  change v + 2 ^ 256 * _ = _ at e
  clear_value v c2 c1 c0
  have h0 := a0.isLt; have h1 := a1.isLt; have h2 := a2.isLt; have h3 := a3.isLt
  have hz : (0 : Word).toNat = 0 := rfl
  simp only [val4, hz, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e
  have hv : val4 a0 a1 a2 a3 = v + P * (a3.toNat / 2 ^ 63) := by
    simp only [val4, P]
    omega
  exact ⟨by rw [hv, Nat.add_mul_mod_self_left], by omega⟩

theorem add19_top (a0 a1 a2 a3 : Word) (hx : val4 a0 a1 a2 a3 < 2 ^ 255 + 19) :
    let c0 := carryOut a0 19 false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let w3 := addCarry a3 0 c2
    0 - w3 >>> 63 = mask (decide (P ≤ val4 a0 a1 a2 a3)) ∧
    (P ≤ val4 a0 a1 a2 a3 → val4 (addCarry a0 19 false) (addCarry a1 0 c0)
      (addCarry a2 0 c1) (w3 &&& 0x7fffffffffffffff) = val4 a0 a1 a2 a3 - P) := by
  intro c0 c1 c2 w3
  have e := add4_value a0 a1 a2 a3 19 0 0 0 false
  change val4 _ _ _ w3 + 2 ^ 256 * _ = _ at e
  clear_value w3 c2
  generalize addCarry a0 19 false = w0 at e ⊢
  generalize addCarry a1 0 c0 = w1 at e ⊢
  generalize addCarry a2 0 c1 = w2 at e ⊢
  have hb : (19 : Word).toNat = 19 := rfl
  have hz : (0 : Word).toNat = 0 := rfl
  have h0 := w0.isLt; have h1 := w1.isLt; have h2 := w2.isLt; have h3 := w3.isLt
  simp only [val4, hb, hz, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e hx ⊢
  have ht : (w3 >>> 63).toNat = w3.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl := and_low63 w3
  by_cases h : P ≤ a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
  · have h1' : w3.toNat / 2 ^ 63 = 1 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (1 : Word).toNat by rw [ht, h1']; rfl),
      decide_eq_true h]
    refine ⟨by decide, fun _ => ?_⟩
    rw [hl]
    simp only [P] at h ⊢
    omega
  · have h0' : w3.toNat / 2 ^ 63 = 0 := by simp only [P] at h; omega
    rw [BitVec.eq_of_toNat_eq (show (w3 >>> 63).toNat = (0 : Word).toNat by rw [ht, h0']; rfl),
      decide_eq_false h]
    exact ⟨by decide, fun h' => absurd h' h⟩

end VG.Proof.Ed25519.Word64
