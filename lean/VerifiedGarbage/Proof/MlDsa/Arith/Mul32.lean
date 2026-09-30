import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-!
# ML-DSA: products modulo `q` with 32-bit multiplications, for every target

Untrusted: everything here is checked by Lean. A target whose only
multiplication keeps the low 32 bits of the product (32-bit ARM, see
`TCB/Arm/Isa.lean`) cannot form the product of two reduced values, which
has up to 46 bits. It multiplies `b < q` by `z < 2²³` by Horner's rule on
the pieces `z₂ = ⌊z / 2¹⁴⌋ < 2⁹`, `z₁ = ⌊z / 2⁷⌋ mod 2⁷` and `z₀ = z mod 2⁷`
of `z`, reducing after each step with `red23`, `x - ⌊x / 2²³⌋ · q`, which
is congruent to `x` and, for `x < 2³²`, at most `2²³ - 1 + 511 · 8191`
(`red23_le`) as `2²³ - q = 8191`:

`mulzN b z = red23 (b z₀ + 2⁷ · red23 (b z₁ + 2⁷ · red23 (b z₂)))`

is congruent to `b · z` (`mulzN_mod`), and every value on the way is less
than `2³²` (`mulzN_bounds`), and the result less than `2q`.
-/

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- `x - ⌊x / 2²³⌋ · q`. -/
def red23 (x : Nat) : Nat := x - x / 2 ^ 23 * q

/-- The largest value of `red23` on 32 bits. -/
def redMax : Nat := 12574208

theorem red23_le {x : Nat} (hx : x < 2 ^ 32) : red23 x ≤ redMax := by
  unfold red23 redMax; rw [q_eq]; omega

theorem red23_mod (x : Nat) : red23 x % q = x % q := by
  unfold red23
  rw [Nat.mul_comm]
  exact Nat.sub_mul_mod (by rw [q_eq]; omega)

/-- `(a + x · c) mod q` depends only on `x mod q`. -/
theorem add_mul_mod_congr (a c : Nat) {x y : Nat} (h : x % q = y % q) :
    (a + x * c) % q = (a + y * c) % q := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

/-- The first step of the product: `red23 (b z₂)`. -/
def mulz1 (b z : Nat) : Nat := red23 (b * (z / 16384))

/-- The second step: `red23 (b z₁ + 2⁷ · …)`. -/
def mulz2 (b z : Nat) : Nat := red23 (b * (z / 128 % 128) + mulz1 b z * 128)

/-- `b · z` modulo `q`, less than `2q`, by Horner's rule on the pieces of `z`. -/
def mulzN (b z : Nat) : Nat := red23 (b * (z % 128) + mulz2 b z * 128)

theorem mulzN_mod (b z : Nat) : mulzN b z % q = b * z % q := by
  unfold mulzN mulz2 mulz1
  have e1 : (b * (z / 128 % 128) + red23 (b * (z / 16384)) * 128) % q =
      (b * (z / 128 % 128) + b * (z / 16384) * 128) % q := add_mul_mod_congr _ _ (red23_mod _)
  rw [red23_mod, add_mul_mod_congr _ _ ((red23_mod _).trans e1)]
  have hz : z % 128 + (z / 128 % 128 + z / 16384 * 128) * 128 = z := by omega
  conv => rhs; rw [← hz]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- The values on the way to `mulzN b z` fit in 32 bits, and the result is
less than `2q`. -/
theorem mulzN_bounds {b z : Nat} (hb : b < q) (hz : z < 2 ^ 23) :
    b * (z / 16384) < 2 ^ 32 ∧ b * (z / 128 % 128) + mulz1 b z * 128 < 2 ^ 32 ∧
      b * (z % 128) + mulz2 b z * 128 < 2 ^ 32 ∧ mulzN b z ≤ redMax := by
  rw [q_eq] at hb
  have h2 : b * (z / 16384) ≤ 8380416 * 511 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1 : b * (z / 128 % 128) ≤ 8380416 * 127 := Nat.mul_le_mul (by omega) (by omega)
  have h0 : b * (z % 128) ≤ 8380416 * 127 := Nat.mul_le_mul (by omega) (by omega)
  have r1 : mulz1 b z ≤ redMax := red23_le (by omega)
  have r2 : mulz2 b z ≤ redMax := red23_le (by unfold redMax at r1; omega)
  unfold redMax at r1 r2
  exact ⟨by omega, by omega, by omega, red23_le (by omega)⟩

theorem redMax_lt : redMax < 2 * q := by decide

end VG.Proof.MlDsa.Arith
