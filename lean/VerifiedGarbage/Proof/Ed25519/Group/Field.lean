import VerifiedGarbage.Proof.Ed25519.Group.Prime
import VerifiedGarbage.Proof.Ed25519.Group.EdwardsGroup
import VerifiedGarbage.Spec.Ed25519
import Mathlib.FieldTheory.Finite.Basic

/-!
# The specification's field as `ZMod P`, and the curve's parameters

Untrusted. `Fe = Fin P` and `ZMod P` are the same type with the same
operations, so `toZ` is the identity; `ZMod P` is a field because `P` is
prime (`Prime.lean`). The specification's `d` is not a square (its power
`(P - 1) / 2` is `-1`) and `sqrtM1` squares to `-1`, so the Edwards addition
law over `ZMod P` is complete.
-/

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe P)
open Edwards

/-- An element of `Fe` as an element of the field `ZMod P`. -/
def toZ (a : Fe) : ZMod P := a

theorem toZ_add (a b : Fe) : toZ (a + b) = toZ a + toZ b := rfl
theorem toZ_sub (a b : Fe) : toZ (a - b) = toZ a - toZ b := rfl
theorem toZ_mul (a b : Fe) : toZ (a * b) = toZ a * toZ b := rfl
theorem toZ_zero : toZ 0 = 0 := rfl
theorem toZ_one : toZ 1 = 1 := rfl
theorem toZ_two : toZ 2 = 2 := rfl
theorem toZ_inj {a b : Fe} : toZ a = toZ b ↔ a = b := Iff.rfl

theorem toZ_pow (a : Fe) (e : Nat) : toZ (Spec.X25519.pow a e) = toZ a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [Spec.X25519.pow]
    by_cases h0 : e = 0
    · subst h0; rfl
    · simp only [h0, ↓reduceIte]
      have hlt : e / 2 < e := Nat.div_lt_self (by omega) (by decide)
      have hsplit : toZ a ^ e = (toZ a * toZ a) ^ (e / 2) * toZ a ^ (e % 2) := by
        rw [← sq, ← pow_mul, ← pow_add]; congr 1; omega
      by_cases h2 : e % 2 = 0
      · simp only [h2, ↓reduceIte]
        rw [ih _ hlt, toZ_mul, hsplit, h2, pow_zero, mul_one]
      · simp only [h2, ↓reduceIte]
        rw [toZ_mul, ih _ hlt, toZ_mul, hsplit, show e % 2 = 1 by omega, pow_one, mul_comm]

/-- The curve parameter `d` in `ZMod P`. -/
def dZ : ZMod P := toZ Spec.Ed25519.d

private theorem d_val : (Spec.Ed25519.d : Fe).val =
    37095705934669439343138083508754565189542113879843219016388785533085940283555 := by
  decide +kernel

private theorem d_pow : powMod P 256 37095705934669439343138083508754565189542113879843219016388785533085940283555
    ((P - 1) / 2) = P - 1 := by decide +kernel

theorem dZ_pow : dZ ^ ((P - 1) / 2) = -1 := by
  have h : dZ = ((37095705934669439343138083508754565189542113879843219016388785533085940283555 : Nat) :
      ZMod P) := by
    rw [← d_val]; exact (ZMod.natCast_zmod_val _).symm
  rw [h, ← powMod_cast P 256 _ _ (by decide), d_pow, Nat.cast_sub (by decide), ZMod.natCast_self,
    Nat.cast_one, zero_sub]

private theorem sqrtM1_sq : Spec.Ed25519.sqrtM1 * Spec.Ed25519.sqrtM1 = 0 - 1 := by decide +kernel

theorem params : Params dZ where
  two := by
    intro h
    have : ((2 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    exact absurd this (by decide)
  sqrtm1 := ⟨toZ Spec.Ed25519.sqrtM1, by
    rw [sq, ← toZ_mul, sqrtM1_sq, toZ_sub, toZ_zero, toZ_one, zero_sub]⟩
  nonsq r hr := by
    have hd : dZ ≠ 0 := by
      intro h; have := dZ_pow; rw [h, zero_pow (by decide)] at this
      exact absurd this (by
        intro h'
        have : ((1 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by
          rw [Nat.cast_one, Nat.cast_zero, ← neg_eq_zero, ← h']
        rw [ZMod.natCast_eq_natCast_iff'] at this
        exact absurd this (by decide))
    have hr0 : r ≠ 0 := by rintro rfl; apply hd; rw [← hr]; ring
    have h1 := ZMod.pow_card_sub_one_eq_one hr0
    have h2 := dZ_pow
    rw [← hr, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide, h1] at h2
    have : ((2 : Nat) : ZMod P) = ((0 : Nat) : ZMod P) := by
      rw [Nat.cast_ofNat, Nat.cast_zero]; linear_combination h2
    rw [ZMod.natCast_eq_natCast_iff'] at this
    exact absurd this (by decide)

instance fact_params : Fact (Params dZ) := ⟨params⟩

end VG.Proof.Ed25519
