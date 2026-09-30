import VerifiedGarbage.Proof.Framework.Omega

/-! Target-independent unsigned word arithmetic for the Ed25519 ports. -/
namespace VG.Proof.Ed25519.Word64

abbrev Word := BitVec 64

def addCarry (a b : Word) (c : Bool) : Word := a + b + BitVec.ofNat 64 c.toNat
def carryOut (a b : Word) (c : Bool) : Bool := decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)

abbrev val4 (a b c d : Word) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

theorem val4_lt (a b c d : Word) : val4 a b c d < 2 ^ 256 := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [val4]
  omega

theorem low_le_val4 (a b c d : Word) : a.toNat ≤ val4 a b c d := by
  simp only [val4]
  omega

theorem carryWord (c : Bool) : (BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
  cases c <;> rfl

theorem carry38_value (c : Bool) : (addCarry 0 0 c * 38).toNat = 38 * c.toNat := by
  cases c <;> decide

theorem borrow_mask (c : Bool) : addCarry 0 (~~~0) c = if c then 0 else -1 := by
  cases c <;> decide

theorem borrow38_value (c : Bool) :
    (addCarry 0 (~~~0) c &&& 38).toNat = 38 * (1 - c.toNat) := by
  cases c <;> decide

theorem addCarry_value (a b : Word) (c : Bool) :
    (addCarry a b c).toNat + 2 ^ 64 * (carryOut a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  simp only [addCarry, BitVec.toNat_add, carryWord, carryOut]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Complemented addition implements subtraction with C as *no borrow*. -/
theorem subCarry_value (a b : Word) (c : Bool) :
    (addCarry a (~~~b) c).toNat + b.toNat + (1 - c.toNat) =
      a.toNat + 2 ^ 64 * (1 - (carryOut a (~~~b) c).toNat) := by
  have h := addCarry_value a (~~~b) c
  have hb := b.isLt
  have hc := Bool.toNat_le c
  have hd := Bool.toNat_le (carryOut a (~~~b) c)
  simp only [BitVec.toNat_not] at h
  omega

theorem addCarry_false (a b : Word) : addCarry a b false = a + b := by
  change a + b + 0 = a + b
  exact BitVec.add_zero _

theorem carryOut_false (a b : Word) :
    carryOut a b false = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  simp only [carryOut, Bool.toNat_false, Nat.add_zero]

theorem addCarry_sub (a b : Word) (c : Bool) :
    addCarry a (~~~b) c = a - b - BitVec.ofNat 64 (1 - c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  simp only [addCarry, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_not,
    BitVec.toNat_ofNat]
  omega

/-- Four limbs, including a carry into the low limb and out of the high limb. -/
theorem add4_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (c : Bool) :
    let c0 := carryOut a0 b0 c
    let c1 := carryOut a1 b1 c0
    let c2 := carryOut a2 b2 c1
    let c3 := carryOut a3 b3 c2
    val4 (addCarry a0 b0 c) (addCarry a1 b1 c0) (addCarry a2 b2 c1) (addCarry a3 b3 c2) +
        2 ^ 256 * c3.toNat = val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 + c.toNat := by
  intro c0 c1 c2 c3
  have e0 := addCarry_value a0 b0 c
  have e1 := addCarry_value a1 b1 c0
  have e2 := addCarry_value a2 b2 c1
  have e3 := addCarry_value a3 b3 c2
  dsimp only [c0, c1, c2, c3] at *
  simp only [val4]
  omega

theorem sub4_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (c : Bool) :
    let c0 := carryOut a0 (~~~b0) c
    let c1 := carryOut a1 (~~~b1) c0
    let c2 := carryOut a2 (~~~b2) c1
    let c3 := carryOut a3 (~~~b3) c2
    val4 (addCarry a0 (~~~b0) c) (addCarry a1 (~~~b1) c0)
        (addCarry a2 (~~~b2) c1) (addCarry a3 (~~~b3) c2) +
        val4 b0 b1 b2 b3 + (1 - c.toNat) =
      val4 a0 a1 a2 a3 + 2 ^ 256 * (1 - c3.toNat) := by
  intro c0 c1 c2 c3
  have e0 := subCarry_value a0 b0 c
  have e1 := subCarry_value a1 b1 c0
  have e2 := subCarry_value a2 b2 c1
  have e3 := subCarry_value a3 b3 c2
  dsimp only [c0, c1, c2, c3] at *
  simp only [val4]
  omega

/-- A full 64-by-64 product, plus two words, fits in two words. -/
theorem multiply_accumulate (a b c t : Word) :
    let lo := a * b
    let hi := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)
    let r := addCarry lo c false
    let d := addCarry hi 0 (carryOut lo c false)
    (addCarry t r false).toNat +
        2 ^ 64 * (addCarry d 0 (carryOut t r false)).toNat =
      t.toNat + c.toNat + a.toNat * b.toNat := by
  intro lo hi r d
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlo : lo.toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have hhi : hi.toNat = a.toNat * b.toNat / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hz : (0 : Word).toNat = 0 := rfl
  simp only [r, d, addCarry, carryOut, BitVec.toNat_add, carryWord,
    Bool.toNat_false, BitVec.add_zero, hz, Nat.add_zero, hlo, hhi]
  by_cases h1 : 2 ^ 64 ≤ a.toNat * b.toNat % 2 ^ 64 + c.toNat
  all_goals simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
  all_goals by_cases h2 : 2 ^ 64 ≤ t.toNat + (a.toNat * b.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64
  all_goals simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
  all_goals omega

/-- A doubled bounded value cannot carry out of its four limbs. -/
theorem bounded_double {v a c b : Nat} (e : v + 2 ^ 256 * c = a + a + b)
    (h : 2 * a + b < 2 ^ 256) : v = 2 * a + b := by omega

end VG.Proof.Ed25519.Word64
