import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Spec.Weierstrass

/-!
# Certificates that a cubic has no root modulo a prime

A curve has no point of order 2 if `f = x³ + a x + b` has no root in
`GF(p)`. A root `r` would satisfy `r^p = r` (Fermat), and `r^p = g(r)` for
`g = x^p mod f`, so `r` would be a root of `h = g - x` too; an inverse `v` of
`h` modulo `f` (`v h ≡ 1`) rules that out, since then `v(r) h(r) = 1`.

The kernel computes `g` and checks `v h ≡ 1` (`decide +kernel`) in
`ZMod p [x] / (x³ - A x - B)` (with `A = -a`, `B = -b`), whose elements are
triples of `Nat`s `c₀ + c₁ x + c₂ x²` (`mulT`, `powT`); evaluating at a root
of `x³ - A x - B` is a ring homomorphism (`evalT_mulT`).
-/

namespace VG.Proof.Weierstrass

/-- `c₀ + c₁ x + c₂ x²`. -/
abbrev Tri := Nat × Nat × Nat

/-- The product in `ZMod p [x] / (x³ - A x - B)`: `x³ = A x + B` and
`x⁴ = A x² + B x`. -/
def mulT (p A B : Nat) (u v : Tri) : Tri :=
  let d0 := u.1 * v.1
  let d1 := u.1 * v.2.1 + u.2.1 * v.1
  let d2 := u.1 * v.2.2 + u.2.1 * v.2.1 + u.2.2 * v.1
  let d3 := u.2.1 * v.2.2 + u.2.2 * v.2.1
  let d4 := u.2.2 * v.2.2
  ((d0 + d3 * B) % p, (d1 + d3 * A + d4 * B) % p, (d2 + d4 * A) % p)

/-- `u ^ e` for `e < 2 ^ n`, by binary exponentiation. -/
def powT (p A B : Nat) : Nat → Tri → Nat → Tri
  | 0, _, _ => (1, 0, 0)
  | n + 1, u, e => if e = 0 then (1, 0, 0) else
      if e % 2 = 0 then powT p A B n (mulT p A B u u) (e / 2)
      else mulT p A B u (powT p A B n (mulT p A B u u) (e / 2))

section
variable {p : Nat}

/-- Evaluation at `r`. -/
def evalT (r : ZMod p) (u : Tri) : ZMod p := u.1 + u.2.1 * r + u.2.2 * r ^ 2

variable {A B : Nat} {r : ZMod p} (hr : r ^ 3 = A * r + B)
include hr

theorem evalT_mulT (u v : Tri) : evalT r (mulT p A B u v) = evalT r u * evalT r v := by
  simp only [evalT, mulT, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  linear_combination (-((u.2.1 * v.2.2 + u.2.2 * v.2.1 : ZMod p) + u.2.2 * v.2.2 * r)) * hr

theorem evalT_powT (n : Nat) (u : Tri) (e : Nat) (he : e < 2 ^ n) :
    evalT r (powT p A B n u e) = evalT r u ^ e := by
  have h1 : evalT r ((1, 0, 0) : Tri) = 1 := by
    simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
  induction n generalizing u e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; rw [powT, h1, _root_.pow_zero]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0; rw [powT, ite_eq_left rfl, h1, _root_.pow_zero]
    have he2 : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hsplit : evalT r u ^ e = (evalT r u * evalT r u) ^ (e / 2) * evalT r u ^ (e % 2) := by
      rw [← sq, ← pow_mul, ← pow_add]; congr 1; omega
    rw [powT, ite_eq_right h0]
    by_cases h2 : e % 2 = 0
    · rw [ite_eq_left h2, ih _ _ he2, evalT_mulT hr, hsplit, h2, _root_.pow_zero, mul_one]
    · rw [ite_eq_right h2, evalT_mulT hr, ih _ _ he2, evalT_mulT hr, hsplit,
        show e % 2 = 1 by omega, pow_one, mul_comm]

end

/-- `x³ = A x + B` has no root modulo the prime `p`, given `g = x^p` and an
inverse `v` of `g - x`, modulo `x³ - A x - B`. -/
theorem noRoot_of_cert (p A B n : Nat) [Fact p.Prime] (hn : p < 2 ^ n) (g v : Tri)
    (hg : powT p A B n (0, 1, 0) p = g)
    (hv : mulT p A B v (g.1, (g.2.1 + p - 1) % p, g.2.2) = (1, 0, 0)) :
    ∀ r : ZMod p, r ^ 3 ≠ A * r + B := by
  intro r hr
  have hx : evalT r ((0, 1, 0) : Tri) = r := by
    simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, one_mul, zero_add]
  have hgr : evalT r g = r := by
    rw [← hg, evalT_powT hr _ _ _ hn, hx, ZMod.pow_card]
  have hh : evalT r ((g.1, (g.2.1 + p - 1) % p, g.2.2) : Tri) = 0 := by
    have hp1 : 1 ≤ g.2.1 + p := by have := (Fact.out : p.Prime).one_lt; omega
    have : evalT r ((g.1, (g.2.1 + p - 1) % p, g.2.2) : Tri) = evalT r g - r := by
      simp only [evalT, ZMod.natCast_mod, Nat.cast_sub hp1, Nat.cast_add, ZMod.natCast_self,
        Nat.cast_one]
      ring
    rw [this, hgr, sub_self]
  have := evalT_mulT hr v (g.1, (g.2.1 + p - 1) % p, g.2.2)
  rw [hv, hh, mul_zero] at this
  simp only [evalT, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] at this
  exact one_ne_zero this

open Spec.Weierstrass in
/-- A curve has no point of order 2, given the certificate of `noRoot_of_cert`
for `A = -a` and `B = -b`. -/
theorem noTwoTorsion_of_cert (C : Curve) [Fact C.p.Prime] (A B n : Nat)
    (hA : (A + C.a) % C.p = 0) (hB : (B + C.b) % C.p = 0) (hn : C.p < 2 ^ n) (g v : Tri)
    (hg : powT C.p A B n (0, 1, 0) C.p = g)
    (hv : mulT C.p A B v (g.1, (g.2.1 + C.p - 1) % C.p, g.2.2) = (1, 0, 0)) :
    ∀ x : ZMod C.p, x ^ 3 + (C.a : ZMod C.p) * x + (C.b : ZMod C.p) ≠ 0 := by
  intro x hx
  have hA' : (A : ZMod C.p) + C.a = 0 := by
    rw [← Nat.cast_add, ← ZMod.natCast_mod, hA, Nat.cast_zero]
  have hB' : (B : ZMod C.p) + C.b = 0 := by
    rw [← Nat.cast_add, ← ZMod.natCast_mod, hB, Nat.cast_zero]
  exact noRoot_of_cert C.p A B n hn g v hg hv x (by linear_combination hx - x * hA' - hB')

end VG.Proof.Weierstrass
