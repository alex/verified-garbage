import VerifiedGarbage.Proof.X448.Wide.Product

/-!
# Carrying a product's coefficients

Untrusted: everything here is checked by Lean. Coefficients `0`–`3` carry
into each other and into `4`, and `4`–`7` into each other and, by
`2⁴⁴⁸ = 2²²⁴ + 1 (mod p)`, into `0` and `4`; one more carry from `0` and `4`
into `1` and `5` leaves limbs within `2⁵⁶ + 2⁸`. `out` describes the limbs,
`out_val` their value.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG.Spec.X448
open VG.Proof.X448.Wide (valN valN_succ radix half full)

/-- The carry into coefficient `lo + n` of the chain from `lo`. -/
def chain (r : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (r (lo + n) + chain r lo n) / radix

/-- Limb `lo + n` of the chain from `lo`. -/
def chainLimb (r : Nat → Nat) (lo n : Nat) : Nat := (r (lo + n) + chain r lo n) % radix

/-- The limbs after both chains and the final carries. -/
def out (r : Nat → Nat) (i : Nat) : Nat :=
  let c₀ := chainLimb r 0 0 + chain r 4 4
  let c₄ := chainLimb r 4 0 + chain r 0 4 + chain r 4 4
  match i with
  | 0 => c₀ % radix
  | 1 => chainLimb r 0 1 + c₀ / radix
  | 2 => chainLimb r 0 2
  | 3 => chainLimb r 0 3
  | 4 => c₄ % radix
  | 5 => chainLimb r 4 1 + c₄ / radix
  | 6 => chainLimb r 4 2
  | _ => chainLimb r 4 3

theorem chain_val (r : Nat → Nat) (lo n : Nat) :
    valN (fun k => chainLimb r lo k) n + radix ^ n * chain r lo n = valN (fun k => r (lo + k)) n := by
  induction n with
  | zero => simp only [valN, chain, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (r (lo + n) + chain r lo n) radix
    simp only [valN_succ, chain, chainLimb] at hd ih ⊢
    rw [Nat.pow_succ, ← ih]
    generalize radix ^ n = X at *
    have : X * ((r (lo + n) + chain r lo n) % radix) +
        X * radix * ((r (lo + n) + chain r lo n) / radix) =
        X * r (lo + n) + X * chain r lo n := by
      rw [Nat.mul_assoc, ← Nat.mul_add, hd, Nat.mul_add]
    rw [Nat.add_assoc, this]
    ac_rfl

theorem out_val (r : Nat → Nat) :
    valN (out r) 8 + P * chain r 4 4 = valN r 8 := by
  have hl := chain_val r 0 4
  have hh := chain_val r 4 4
  have h0 := Nat.mod_add_div (chainLimb r 0 0 + chain r 4 4) radix
  have h4 := Nat.mod_add_div (chainLimb r 4 0 + chain r 0 4 + chain r 4 4) radix
  have hp : P = radix ^ 8 - radix ^ 4 - 1 := by decide +kernel
  simp only [valN, out, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, Nat.pow_zero, Nat.one_mul] at hl hh ⊢
  simp only [hp, radix, Nat.reducePow] at hl hh h0 h4 ⊢
  omega

/-- The value modulo `p`. -/
theorem out_mod (r : Nat → Nat) : valN (out r) 8 % P = valN r 8 % P := by
  rw [← out_val r, Nat.add_mul_mod_self_left]

end VG.Proof.Curve448.AArch64.Fast
