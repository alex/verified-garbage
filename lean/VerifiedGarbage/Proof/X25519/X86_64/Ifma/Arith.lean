import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Mul
import VerifiedGarbage.Proof.X25519.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# X25519 on x86-64 with AVX512_IFMA: the arithmetic of the lanes

Untrusted: everything here is checked by Lean. A field element is five limbs
`x₀ + 2⁵¹ x₁ + … + 2²⁰⁴ x₄` (`lv`), standing for its residue modulo `p`.
The identities between limbs are polynomial identities in `R = 2⁵¹`
(`2⁵² = 2R`, `2²⁵⁵ = R⁵`), proved as such.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG.Proof.X25519 VG.Spec.X25519

/-- The number five limbs stand for. -/
def lv (x : Nat → Nat) : Nat := x 0 + 2 ^ 51 * x 1 + 2 ^ 102 * x 2 + 2 ^ 153 * x 3 + 2 ^ 204 * x 4

/-- `lv` in `R = 2⁵¹`. -/
def lvR (R : Nat) (x : Nat → Nat) : Nat := x 0 + R * x 1 + R ^ 2 * x 2 + R ^ 3 * x 3 + R ^ 4 * x 4

theorem lv_eq (x : Nat → Nat) : lv x = lvR (2 ^ 51) x := by
  simp only [lv, lvR, ← Nat.pow_mul]

/-- The columns `c` of a product `x · y` (of numbers below `2R`, here `2⁵²`),
as `accLo` and `accHi` sum them: the low halves of the products `x_i y_j`
with `i + j = c` and the high halves with `i + j + 1 = c`. -/
def colR (R : Nat) (x y : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + x i * y (c - i) % (2 * R) else acc) 0 +
  (List.range 5).foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + x i * y (c - (i + 1)) / (2 * R) else acc) 0 * 2

/-- The product identity: `Σ_c col_c Rᶜ = x · y`, with columns `5–9`
separated (`lo + R⁵ hi`). -/
theorem colR_eq (R : Nat) (x y : Nat → Nat) :
    (colR R x y 0 + R * colR R x y 1 + R ^ 2 * colR R x y 2 + R ^ 3 * colR R x y 3 +
      R ^ 4 * colR R x y 4) +
    R ^ 5 * (colR R x y 5 + R * colR R x y 6 + R ^ 2 * colR R x y 7 + R ^ 3 * colR R x y 8 +
      R ^ 4 * colR R x y 9) = lvR R x * lvR R y := by
  have h00 := Nat.mod_add_div (x 0 * y 0) (2 * R)
  have h01 := Nat.mod_add_div (x 0 * y 1) (2 * R)
  have h02 := Nat.mod_add_div (x 0 * y 2) (2 * R)
  have h03 := Nat.mod_add_div (x 0 * y 3) (2 * R)
  have h04 := Nat.mod_add_div (x 0 * y 4) (2 * R)
  have h10 := Nat.mod_add_div (x 1 * y 0) (2 * R)
  have h11 := Nat.mod_add_div (x 1 * y 1) (2 * R)
  have h12 := Nat.mod_add_div (x 1 * y 2) (2 * R)
  have h13 := Nat.mod_add_div (x 1 * y 3) (2 * R)
  have h14 := Nat.mod_add_div (x 1 * y 4) (2 * R)
  have h20 := Nat.mod_add_div (x 2 * y 0) (2 * R)
  have h21 := Nat.mod_add_div (x 2 * y 1) (2 * R)
  have h22 := Nat.mod_add_div (x 2 * y 2) (2 * R)
  have h23 := Nat.mod_add_div (x 2 * y 3) (2 * R)
  have h24 := Nat.mod_add_div (x 2 * y 4) (2 * R)
  have h30 := Nat.mod_add_div (x 3 * y 0) (2 * R)
  have h31 := Nat.mod_add_div (x 3 * y 1) (2 * R)
  have h32 := Nat.mod_add_div (x 3 * y 2) (2 * R)
  have h33 := Nat.mod_add_div (x 3 * y 3) (2 * R)
  have h34 := Nat.mod_add_div (x 3 * y 4) (2 * R)
  have h40 := Nat.mod_add_div (x 4 * y 0) (2 * R)
  have h41 := Nat.mod_add_div (x 4 * y 1) (2 * R)
  have h42 := Nat.mod_add_div (x 4 * y 2) (2 * R)
  have h43 := Nat.mod_add_div (x 4 * y 3) (2 * R)
  have h44 := Nat.mod_add_div (x 4 * y 4) (2 * R)
  simp only [colR, lvR, List.range, List.range.loop, List.foldl]
  simp (config := {decide := true}) only [Nat.zero_add, ite_true, ite_false]
  zify at *
  linear_combination R ^ 0 * h00 + R ^ 1 * h01 + R ^ 2 * h02 + R ^ 3 * h03 + R ^ 4 * h04 + R ^ 1 * h10 + R ^ 2 * h11 + R ^ 3 * h12 + R ^ 4 * h13 + R ^ 5 * h14 + R ^ 2 * h20 + R ^ 3 * h21 + R ^ 4 * h22 + R ^ 5 * h23 + R ^ 6 * h24 + R ^ 3 * h30 + R ^ 4 * h31 + R ^ 5 * h32 + R ^ 6 * h33 + R ^ 7 * h34 + R ^ 4 * h40 + R ^ 5 * h41 + R ^ 6 * h42 + R ^ 7 * h43 + R ^ 8 * h44

theorem accLo_eq (a b : Nat → Nat) (c : Nat) :
    accLo a b c = (List.range 5).foldl (fun acc i =>
      if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % (2 * 2 ^ 51) else acc) 0 := rfl

theorem accHi_eq (a b : Nat → Nat) (c : Nat) :
    accHi a b c = (List.range 5).foldl (fun acc i =>
      if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / (2 * 2 ^ 51)
      else acc) 0 := rfl

theorem mulNat_col (a b : Nat → Nat) (k : Nat) :
    mulNat a b k = colR (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52) k +
      19 * colR (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52) (k + 5) := by
  simp only [mulNat, colR, accLo_eq, accHi_eq]
  omega

/-- `mul4`'s limbs stand for the product of the low 52 bits of the limbs, modulo `p`. -/
theorem mulNat_mod (a b : Nat → Nat) :
    lv (mulNat a b) % P = lv (fun i => a i % 2 ^ 52) * lv (fun j => b j % 2 ^ 52) % P := by
  have e := colR_eq (2 ^ 51) (fun i => a i % 2 ^ 52) (fun j => b j % 2 ^ 52)
  rw [lv_eq, lv_eq, lv_eq, ← e, show (2 ^ 51 : Nat) ^ 5 = 2 ^ 255 by rfl, fold255]
  simp only [lvR, mulNat_col, Nat.zero_add, Nat.reduceAdd]
  congr 1
  omega

end VG.Proof.X25519.X86_64.Ifma
