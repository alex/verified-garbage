import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 arithmetic in radix 2^64

Target-independent bounds, modular reduction and word-carry identities for
three-word accumulators and two-word clamped keys.
-/

open VG.PowLit
namespace VG.Proof.Poly1305.Limbs64
open VG.Spec.Poly1305 (P)

theorem mul_lt {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  Nat.mul_lt_mul_of_lt_of_lt h₁ h₂

theorem mul_le_lt {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c < d) : a * c ≤ b * d :=
  Nat.mul_le_mul h₁ (Nat.le_of_lt h₂)

/-- The bounds that make every sum of products fit its registers. -/
theorem absorb_bounds {h0 h1 h2 r0 q : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6)
    (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58) :
    h0 * r0 < 2 ^ 124 ∧ h1 * (5 * q) < 2 ^ 125 ∧ h0 * (4 * q) < 2 ^ 124 ∧ h1 * r0 < 2 ^ 124 ∧
      h2 * (5 * q) < 2 ^ 64 ∧ h2 * r0 ≤ 6 * r0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_lt hh0 hr0; omega_using [this]
  · have := mul_lt hh1 (show 5 * q < 5 * 2 ^ 58 by omega_using [hq]); omega_using [this]
  · have := mul_lt hh0 (show 4 * q < 4 * 2 ^ 58 by omega_using [hq]); omega_using [this]
  · have := mul_lt hh1 hr0; omega_using [this]
  · have := mul_le_lt hh2 (show 5 * q < 5 * 2 ^ 58 by omega_using [hq]); omega_using [this]
  · exact Nat.mul_le_mul_right _ hh2

/-- `(h0 + 2⁶⁴ h1 + 2¹²⁸ h2) (r0 + 2⁶⁴ 4 q)`, expanded into the named products. -/
theorem expand (h0 h1 h2 r0 q : Nat) :
    (h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q)) =
      h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) := by
  grind

/-- Absorbing a block: `x = x0 + 2⁶⁴ x1 = h0 r0 + h1 s1`, `y = y0 + 2⁶⁴ y1 =
h0 r1 + h1 r0 + h2 s1`, `u0 + 2⁶⁴ c1 = y0 + x1`, the top word `t = y1 + h2 r0 +
c1`, and the result `w = x0 + 5 ⌊t / 4⌋ + 2⁶⁴ u0 + 2¹²⁸ (t mod 4)` in three
words: `w ≡ h r` modulo `p`, and `w2 ≤ 4`. -/
theorem absorb_arith {h0 h1 h2 r0 q x0 x1 y0 y1 u0 c1 w0 w1 w2 : Nat}
    (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6) (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58)
    (hx : x0 + 2 ^ 64 * x1 = h0 * r0 + h1 * (5 * q)) (hx0 : x0 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 = h0 * (4 * q) + h1 * r0 + h2 * (5 * q))
    (hu : u0 + 2 ^ 64 * c1 = y0 + x1) (hu0 : u0 < 2 ^ 64)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      x0 + 5 * ((y1 + h2 * r0 + c1) / 4) + 2 ^ 64 * u0 + 2 ^ 128 * ((y1 + h2 * r0 + c1) % 4))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) :
    (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) % P =
      ((h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q))) % P ∧ w2 ≤ 4 := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds hh0 hh1 hh2 hr0 hq
  have e5 : h1 * (5 * q) = 5 * (h1 * q) := Nat.mul_left_comm _ _ _
  have e4 : h0 * (4 * q) = 4 * (h0 * q) := Nat.mul_left_comm _ _ _
  have e5' : h2 * (5 * q) = 5 * (h2 * q) := Nat.mul_left_comm _ _ _
  rw [expand]
  refine ⟨?_, ?_⟩
  · rw [show h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) =
        (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) +
          P * ((y1 + h2 * r0 + c1) / 4 + h1 * q + 2 ^ 64 * (h2 * q)) by
      simp only [P]; omega_using [hx, hy, hu, hw, e5, e5'], Nat.add_mul_mod_self_left]
  · omega_using [hr0, hx, hx0, hy, hu, hu0, hw, hw0, hw1, b1, b2, b3, b4, b5, b6, e5, e4, e5']

/-- Adding a block `m0 + 2⁶⁴ m1 + 2¹²⁸ pad` to `h` with `h2 ≤ 4`: the result's
top word is at most 6. -/
theorem add_arith {h0 h1 h2 m0 m1 pad w0 w1 w2 : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64)
    (hh2 : h2 ≤ 4) (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hpad : pad ≤ 1)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2 + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * pad))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) : w2 ≤ 6 := by
  omega_using [hh0, hh1, hh2, hm0, hm1, hpad, hw, hw0, hw1]


theorem toNat_mul_lo (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have := mul_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])]
  omega_using []

theorem carry_toNat (c : Bool) :
    ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

/-- An addition, with its carry out. -/
theorem addc0 (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  have ha := a.isLt; have hb := b.isLt
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [ha, hb, h]

/-- An addition with carry in, with its carry out. -/
theorem addc1 (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, carry_toNat, Nat.mod_add_mod]
  have ha := a.isLt; have hb := b.isLt; have hc := Bool.toNat_le c
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [ha, hb, hc, h]

/-- An addition with carry into a second word, as numbers, when the sum fits. -/
theorem add_adc_toNat (a b c d : BitVec 64)
    (h : a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) < 2 ^ 128) :
    (a + b).toNat + 2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) := by
  have h1 := addc0 a b
  have h2 := addc1 c d (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  have k1 := Bool.toNat_le (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  omega_using [h, h1, h2, k1]

/-- Three words added with carries, as numbers, when the sum fits. -/
theorem add3_toNat (a b c d e f : BitVec 64)
    (h : a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) + 2 ^ 128 * (e.toNat + f.toNat) < 2 ^ 192) :
    (a + b).toNat +
      2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat +
      2 ^ 128 * (e + f + (BitVec.ofBool (decide (2 ^ 64 ≤ c.toNat + d.toNat +
        (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat))).setWidth 64).toNat =
    a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat) + 2 ^ 128 * (e.toNat + f.toNat) := by
  have h1 := addc0 a b
  have h2 := addc1 c d (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  have h3 := addc1 e f (decide (2 ^ 64 ≤ c.toNat + d.toNat + (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat))
  have k1 := Bool.toNat_le (decide (2 ^ 64 ≤ a.toNat + b.toNat))
  have k2 := Bool.toNat_le
    (decide (2 ^ 64 ≤ c.toNat + d.toNat + (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat))
  omega_using [h, h1, h2, h3, k1, k2]

theorem and3_toNat (x : BitVec 64) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

end VG.Proof.Poly1305.Limbs64
