import Mathlib.FieldTheory.Finite.Basic
import VerifiedGarbage.Spec.Weierstrass

/-!
# The specification's field `Fin p` as `ZMod p`

The specification computes with `Fin m`, arithmetic modulo `m`; the proofs
compute in `ZMod m`, which is a field when `m` is prime. `toF` maps one to
the other: it is an injective ring homomorphism, maps the specification's
`pow` to powers (for any modulus, as ECDSA's scalars modulo `n` need), and,
for a prime `p > 2`, its `inv` to the field's inverse (Fermat's little
theorem; `inv 0 = 0`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

section
variable {m : Nat}

/-- An element of `Fin m` as an element of `ZMod m`. -/
def toF (x : Fin m) : ZMod m := (x.val : ZMod m)

theorem toF_add (x y : Fin m) : toF (x + y) = toF x + toF y := by
  rw [toF, toF, toF, Fin.val_add, ZMod.natCast_mod, Nat.cast_add]

theorem toF_mul (x y : Fin m) : toF (x * y) = toF x * toF y := by
  rw [toF, toF, toF, Fin.val_mul, ZMod.natCast_mod, Nat.cast_mul]

theorem toF_sub (x y : Fin m) : toF (x - y) = toF x - toF y := by
  rw [toF, toF, toF, Fin.sub_def, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub y.isLt.le, ZMod.natCast_self]
  ring

theorem toF_neg (x : Fin m) : toF (-x) = -toF x := by
  rw [toF, toF, Fin.neg_def, ZMod.natCast_mod, Nat.cast_sub x.isLt.le, ZMod.natCast_self,
    zero_sub]

theorem toF_injective : Function.Injective (toF : Fin m → ZMod m) := by
  intro x y h
  have := (ZMod.natCast_eq_natCast_iff' _ _ m).mp h
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at this
  exact Fin.ext this

theorem toF_inj {x y : Fin m} : toF x = toF y ↔ x = y := toF_injective.eq_iff

theorem val_toF (x : Fin m) : (toF x).val = x.val := by
  rw [toF, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]

variable [NeZero m]

theorem toF_ofNat (a : Nat) : toF (Fin.ofNat m a) = (a : ZMod m) := by
  rw [toF, Fin.val_ofNat, ZMod.natCast_mod]

theorem toF_zero : toF (0 : Fin m) = 0 := by
  rw [toF, Fin.val_zero, Nat.cast_zero]

theorem toF_one : toF (1 : Fin m) = 1 := by
  rw [toF, Fin.val_one', ZMod.natCast_mod, Nat.cast_one]

/-- Numerals: `toF 2 = 2`, `toF 3 = 3`, …. -/
theorem toF_ofNat' (a : Nat) [a.AtLeastTwo] : toF (OfNat.ofNat a : Fin m) = OfNat.ofNat a := by
  show toF (Fin.ofNat m a) = _
  rw [toF_ofNat]
  exact (Nat.cast_ofNat : ((OfNat.ofNat a : ℕ) : ZMod m) = OfNat.ofNat a)

theorem toF_pow (x : Fin m) (e : Nat) : toF (pow x e) = toF x ^ e := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [pow]
    by_cases h0 : e = 0
    · subst h0; simp only [↓reduceIte]; rw [toF_one, _root_.pow_zero]
    · simp only [h0, ↓reduceIte]
      have hlt : e / 2 < e := Nat.div_lt_self (by omega) (by decide)
      have hsplit : toF x ^ e = (toF x * toF x) ^ (e / 2) * toF x ^ (e % 2) := by
        rw [← sq, ← pow_mul, ← pow_add]; congr 1; omega
      by_cases h2 : e % 2 = 0
      · simp only [h2, ↓reduceIte]
        rw [ih _ hlt, toF_mul, hsplit, h2, _root_.pow_zero, mul_one]
      · simp only [h2, ↓reduceIte]
        rw [toF_mul, ih _ hlt, toF_mul, hsplit, show e % 2 = 1 by omega, pow_one, mul_comm]

/-- `pow` modulo any `m`, as a power in `ZMod m`. -/
theorem val_pow (x : Fin m) (e : Nat) : ((pow x e).val : ZMod m) = (x.val : ZMod m) ^ e :=
  toF_pow x e

end

section
variable {p : Nat} [Fact p.Prime]

/-- `x ^ (p - 2)` is the inverse in `ZMod p`, for a prime `p > 2` (`0⁻¹ = 0`). -/
theorem pow_sub_two_eq_inv (hp : 2 < p) (z : ZMod p) : z ^ (p - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by omega)]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show p - 2 + 1 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hz]

variable {C : Curve} [Fact C.p.Prime]

theorem toF_inv (hp : 2 < C.p) (x : Fe C) : toF (inv x) = (toF x)⁻¹ := by
  rw [inv, toF_pow, pow_sub_two_eq_inv hp]

theorem inv_zero' (hp : 2 < C.p) : inv (0 : Fe C) = 0 := by
  apply toF_injective
  rw [toF_inv hp, toF_zero, inv_zero]

end

end VG.Proof.Weierstrass
