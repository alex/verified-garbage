import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Steps`.
section

section

/-!
# Poly1305 on AArch64: the arithmetic in radix `2²⁶`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/AArch64.lean`), as natural numbers: five limbs `a0, …, a4`
stand for `val5 a0 a1 a2 a3 a4 = a0 + 2²⁶ a1 + 2⁵² a2 + 2⁷⁸ a3 + 2¹⁰⁴ a4`.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG.Spec.Poly1305 (P)

/-- The number with the limbs `a0, …, a4`. -/
def val5 (a0 a1 a2 a3 a4 : Nat) : Nat := a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4

/-- Limb `j` of `N`: 26 bits, but for the last, which has the rest. -/
def lim (N j : Nat) : Nat := if j < 4 then N / 2 ^ (26 * j) % 2 ^ 26 else N / 2 ^ 104

theorem lim0 (N : Nat) : lim N 0 = N % 2 ^ 26 := by simp only [lim, Nat.zero_lt_succ, ↓reduceIte, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow]
theorem lim1 (N : Nat) : lim N 1 = N / 2 ^ 26 % 2 ^ 26 := by simp only [lim, Nat.reduceLT, ↓reduceIte, Nat.mul_one, Nat.reducePow]
theorem lim2 (N : Nat) : lim N 2 = N / 2 ^ 52 % 2 ^ 26 := by simp only [lim, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reducePow]
theorem lim3 (N : Nat) : lim N 3 = N / 2 ^ 78 % 2 ^ 26 := by simp only [lim, Nat.lt_add_one, ↓reduceIte, Nat.reduceMul, Nat.reducePow]
theorem lim4 (N : Nat) : lim N 4 = N / 2 ^ 104 := by simp only [lim, Nat.lt_irrefl, ↓reduceIte, Nat.reducePow]

theorem val5_lim (N : Nat) : val5 (lim N 0) (lim N 1) (lim N 2) (lim N 3) (lim N 4) = N := by
  simp only [val5, lim0, lim1, lim2, lim3, lim4]
  omega_using []

theorem lim_lt (N : Nat) {j : Nat} (hj : j < 4) : lim N j < 2 ^ 26 := by
  simp only [lim, hj, ite_true]
  exact Nat.mod_lt _ (by decide)

theorem lim4_lt {N : Nat} (h : N < 2 ^ 128) : lim N 4 < 2 ^ 24 := by
  rw [lim4]; omega_using [h]

/-- The limbs `split` computes from the words `lo, hi`. -/
theorem split_arith (lo hi : Nat) (hlo : lo < 2 ^ 64) :
    lo % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 0 ∧
    lo / 2 ^ 26 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 1 ∧
    (lo / 2 ^ 52 + hi * 2 ^ 12 % 2 ^ 64) % 2 ^ 64 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 2 ∧
    hi / 2 ^ 14 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 3 ∧
    hi / 2 ^ 40 = lim (lo + 2 ^ 64 * hi) 4 := by
  simp only [lim0, lim1, lim2, lim3, lim4]
  refine ⟨by omega_using [], by omega_using [], by omega_using [], by omega_using [hlo], by omega_using [hlo]⟩

/-! ## Absorbing a block -/

/-- The sums of products `dk` of the limbs `a` and `r` (with `sj = 5 rj`). -/
theorem product_identity (a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 : Nat) :
    val5 a0 a1 a2 a3 a4 * val5 r0 r1 r2 r3 r4 =
      val5 (a0 * r0 + a1 * (5 * r4) + a2 * (5 * r3) + a3 * (5 * r2) + a4 * (5 * r1))
        (a0 * r1 + a1 * r0 + a2 * (5 * r4) + a3 * (5 * r3) + a4 * (5 * r2))
        (a0 * r2 + a1 * r1 + a2 * r0 + a3 * (5 * r4) + a4 * (5 * r3))
        (a0 * r3 + a1 * r2 + a2 * r1 + a3 * r0 + a4 * (5 * r4))
        (a0 * r4 + a1 * r3 + a2 * r2 + a3 * r1 + a4 * r0) +
      P * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) := by
  have hP : P + 5 = 2 ^ 130 := by simp only [P, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
  have e : val5 a0 a1 a2 a3 a4 * val5 r0 r1 r2 r3 r4 +
      5 * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) =
      val5 (a0 * r0 + a1 * (5 * r4) + a2 * (5 * r3) + a3 * (5 * r2) + a4 * (5 * r1))
        (a0 * r1 + a1 * r0 + a2 * (5 * r4) + a3 * (5 * r3) + a4 * (5 * r2))
        (a0 * r2 + a1 * r1 + a2 * r0 + a3 * (5 * r4) + a4 * (5 * r3))
        (a0 * r3 + a1 * r2 + a2 * r1 + a3 * r0 + a4 * (5 * r4))
        (a0 * r4 + a1 * r3 + a2 * r2 + a3 * r1 + a4 * r0) +
      2 ^ 130 * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) := by
    simp only [val5]; grind
  rw [← hP, Nat.add_mul, ← Nat.add_assoc] at e
  exact Nat.add_right_cancel e

theorem mul_lt' {a b c d : Nat} (h₁ : a < c) (h₂ : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_lt h₁ h₂

/-- The sums of products `products` computes (as `dform` states them), from
the limbs `a` of `h + m` and those of the clamped `R`: they fit in 60 bits,
and they are the limbs of a number congruent to `(h + m) R`. -/
theorem dsum_arith {a0 a1 a2 a3 a4 R : Nat} (ha0 : a0 < 2 ^ 28) (ha1 : a1 < 2 ^ 28)
    (ha2 : a2 < 2 ^ 28) (ha3 : a3 < 2 ^ 28) (ha4 : a4 < 2 ^ 28) (hR : R < 2 ^ 128) :
    let d0 := a0 * lim R 0 + (a1 * (5 * lim R 4) + (a2 * (5 * lim R 3) + (a3 * (5 * lim R 2) +
      (a4 * (5 * lim R 1) + 0))))
    let d1 := a0 * lim R 1 + (a1 * lim R 0 + (a2 * (5 * lim R 4) + (a3 * (5 * lim R 3) +
      (a4 * (5 * lim R 2) + 0))))
    let d2 := a0 * lim R 2 + (a1 * lim R 1 + (a2 * lim R 0 + (a3 * (5 * lim R 4) +
      (a4 * (5 * lim R 3) + 0))))
    let d3 := a0 * lim R 3 + (a1 * lim R 2 + (a2 * lim R 1 + (a3 * lim R 0 + (a4 * (5 * lim R 4) + 0))))
    let d4 := a0 * lim R 4 + (a1 * lim R 3 + (a2 * lim R 2 + (a3 * lim R 1 + (a4 * lim R 0 + 0))))
    d0 < 2 ^ 60 ∧ d1 < 2 ^ 60 ∧ d2 < 2 ^ 60 ∧ d3 < 2 ^ 60 ∧ d4 < 2 ^ 60 ∧
      val5 d0 d1 d2 d3 d4 % P = (val5 a0 a1 a2 a3 a4 * R) % P := by
  intro d0 d1 d2 d3 d4
  have r0 := lim_lt R (j := 0) (by decide); have r1 := lim_lt R (j := 1) (by decide)
  have r2 := lim_lt R (j := 2) (by decide); have r3 := lim_lt R (j := 3) (by decide)
  have r4 := Nat.lt_trans (lim4_lt hR) (show 2 ^ 24 < 2 ^ 26 by decide)
  have e := product_identity a0 a1 a2 a3 a4 (lim R 0) (lim R 1) (lim R 2) (lim R 3) (lim R 4)
  rw [val5_lim] at e
  -- Every product is less than `2⁵⁷`.
  have p : ∀ a j, a < 2 ^ 28 → j < 2 ^ 26 → a * j < 2 ^ 57 ∧ a * (5 * j) < 2 ^ 57 := by
    intro a j ha hj
    have h1 := mul_lt' ha hj
    have h2 := mul_lt' ha (show 5 * j < 5 * 2 ^ 26 by omega_using [hj])
    exact ⟨by omega_using [h1], by omega_using [h2]⟩
  obtain ⟨p00, p00'⟩ := p a0 _ ha0 r0; obtain ⟨p01, p01'⟩ := p a0 _ ha0 r1
  obtain ⟨p02, p02'⟩ := p a0 _ ha0 r2; obtain ⟨p03, p03'⟩ := p a0 _ ha0 r3
  obtain ⟨p04, p04'⟩ := p a0 _ ha0 r4
  obtain ⟨p10, p10'⟩ := p a1 _ ha1 r0; obtain ⟨p11, p11'⟩ := p a1 _ ha1 r1
  obtain ⟨p12, p12'⟩ := p a1 _ ha1 r2; obtain ⟨p13, p13'⟩ := p a1 _ ha1 r3
  obtain ⟨p14, p14'⟩ := p a1 _ ha1 r4
  obtain ⟨p20, p20'⟩ := p a2 _ ha2 r0; obtain ⟨p21, p21'⟩ := p a2 _ ha2 r1
  obtain ⟨p22, p22'⟩ := p a2 _ ha2 r2; obtain ⟨p23, p23'⟩ := p a2 _ ha2 r3
  obtain ⟨p24, p24'⟩ := p a2 _ ha2 r4
  obtain ⟨p30, p30'⟩ := p a3 _ ha3 r0; obtain ⟨p31, p31'⟩ := p a3 _ ha3 r1
  obtain ⟨p32, p32'⟩ := p a3 _ ha3 r2; obtain ⟨p33, p33'⟩ := p a3 _ ha3 r3
  obtain ⟨p34, p34'⟩ := p a3 _ ha3 r4
  obtain ⟨p40, p40'⟩ := p a4 _ ha4 r0; obtain ⟨p41, p41'⟩ := p a4 _ ha4 r1
  obtain ⟨p42, p42'⟩ := p a4 _ ha4 r2; obtain ⟨p43, p43'⟩ := p a4 _ ha4 r3
  obtain ⟨p44, p44'⟩ := p a4 _ ha4 r4
  refine ⟨by omega_using [p00, p14', p23', p32', p41'], by omega_using [p01, p10, p24', p33', p42'],
    by omega_using [p02, p11, p20, p34', p43'], by omega_using [p03, p12, p21, p30, p44'],
    by omega_using [p04, p13, p22, p31, p40], ?_⟩
  rw [e, Nat.add_mul_mod_self_left]
  have : val5 d0 d1 d2 d3 d4 =
      val5 (a0 * lim R 0 + a1 * (5 * lim R 4) + a2 * (5 * lim R 3) + a3 * (5 * lim R 2) +
          a4 * (5 * lim R 1))
        (a0 * lim R 1 + a1 * lim R 0 + a2 * (5 * lim R 4) + a3 * (5 * lim R 3) + a4 * (5 * lim R 2))
        (a0 * lim R 2 + a1 * lim R 1 + a2 * lim R 0 + a3 * (5 * lim R 4) + a4 * (5 * lim R 3))
        (a0 * lim R 3 + a1 * lim R 2 + a2 * lim R 1 + a3 * lim R 0 + a4 * (5 * lim R 4))
        (a0 * lim R 4 + a1 * lim R 3 + a2 * lim R 2 + a3 * lim R 1 + a4 * lim R 0) := by
    simp only [d0, d1, d2, d3, d4, Nat.add_zero, Nat.add_assoc]
  rw [this]

theorem val5_lt {a0 a1 a2 a3 a4 : Nat} (b0 : a0 < 2 ^ 26) (b1 : a1 < 2 ^ 26) (b2 : a2 < 2 ^ 26)
    (b3 : a3 < 2 ^ 26) (b4 : a4 < 2 ^ 26) : val5 a0 a1 a2 a3 a4 < 2 ^ 130 := by
  simp only [val5]; omega_using [b0, b1, b2, b3, b4]

theorem val5_le {a0 a1 a2 a3 a4 : Nat} (b0 : a0 < 2 ^ 26) (b1 : a1 < 2 ^ 26) (b2 : a2 < 2 ^ 26)
    (b3 : a3 < 2 ^ 26) (b4 : a4 ≤ 2 ^ 26) : val5 a0 a1 a2 a3 a4 < 2 ^ 130 + 2 ^ 104 := by
  simp only [val5]; omega_using [b0, b1, b2, b3, b4]

theorem dm26 {x c e : Nat} (hc : c = x / 2 ^ 26) (he : e = x % 2 ^ 26) :
    x = 2 ^ 26 * c + e ∧ e < 2 ^ 26 := by
  subst hc he; exact ⟨(Nat.div_add_mod x _).symm, Nat.mod_lt _ (by decide)⟩

theorem mod64 {x y : Nat} (h : x = y % 2 ^ 64) (hy : y < 2 ^ 64) : x = y :=
  h.trans (Nat.mod_eq_of_lt hy)

/-- The carries of `absorb` (as `carry` computes them): from the sums of
products `d0, …, d4` to the new limbs, `2¹³⁰ ≡ 5` folding the carry `c4` out
of `d4` into the bottom. -/
theorem carry_arith {d0 d1 d2 d3 d4 c0 e0 d1' c1 e1 d2' c2 e2 d3' c2' e3 d4' c4 e4 q c5 f c6 f0 g1 : Nat}
    (h0 : d0 < 2 ^ 60) (h1 : d1 < 2 ^ 60) (h2 : d2 < 2 ^ 60) (h3 : d3 < 2 ^ 60) (h4 : d4 < 2 ^ 60)
    (q0 : c0 = d0 / 2 ^ 26) (q1 : e0 = d0 % 2 ^ 26) (q2 : d1' = (d1 + c0) % 2 ^ 64)
    (q3 : c1 = d1' / 2 ^ 26) (q4 : e1 = d1' % 2 ^ 26) (q5 : d2' = (d2 + c1) % 2 ^ 64)
    (q6 : c2 = d2' / 2 ^ 26) (q7 : e2 = d2' % 2 ^ 26) (q8 : d3' = (d3 + c2) % 2 ^ 64)
    (q9 : c2' = d3' / 2 ^ 26) (q10 : e3 = d3' % 2 ^ 26) (q11 : d4' = (d4 + c2') % 2 ^ 64)
    (q12 : c4 = d4' / 2 ^ 26) (q13 : e4 = d4' % 2 ^ 26) (q14 : q = c4 * 2 ^ 2 % 2 ^ 64)
    (q15 : c5 = (c4 + q) % 2 ^ 64) (q16 : f = (e0 + c5) % 2 ^ 64)
    (q17 : c6 = f / 2 ^ 26) (q18 : f0 = f % 2 ^ 26) (q19 : g1 = (e1 + c6) % 2 ^ 64) :
    val5 f0 g1 e2 e3 e4 + P * c4 = val5 d0 d1 d2 d3 d4 ∧
      f0 < 2 ^ 26 ∧ g1 < 2 ^ 27 ∧ e2 < 2 ^ 26 ∧ e3 < 2 ^ 26 ∧ e4 < 2 ^ 26 := by
  obtain ⟨l0, b0⟩ := dm26 q0 q1
  have C0 : c0 < 2 ^ 34 := by omega_using [h0, l0]
  have r2 := mod64 q2 (by omega_using [h1, C0])
  obtain ⟨l1, b1⟩ := dm26 q3 q4
  have C1 : c1 < 2 ^ 35 := by omega_using [h1, C0, r2, l1]
  have r5 := mod64 q5 (by omega_using [h2, C1])
  obtain ⟨l2, b2⟩ := dm26 q6 q7
  have C2 : c2 < 2 ^ 35 := by omega_using [h2, C1, r5, l2]
  have r8 := mod64 q8 (by omega_using [h3, C2])
  obtain ⟨l3, b3⟩ := dm26 q9 q10
  have C3 : c2' < 2 ^ 35 := by omega_using [h3, C2, r8, l3]
  have r11 := mod64 q11 (by omega_using [h4, C3])
  obtain ⟨l4, b4⟩ := dm26 q12 q13
  have c4b : c4 < 2 ^ 35 := by omega_using [h4, C3, r11, l4]
  have r14 := mod64 q14 (by omega_using [c4b])
  have r15 := mod64 q15 (by omega_using [c4b, r14])
  have r16 := mod64 q16 (by omega_using [c4b, b0, r14, r15])
  obtain ⟨l6, b6⟩ := dm26 q17 q18
  have r19 := mod64 q19 (by omega_using [c4b, b0, b1, r14, r15, r16, l6])
  simp only [val5, P]
  refine ⟨?_, b6, ?_, b2, b3, b4⟩
  · omega_using [l0, r2, l1, r5, l2, r8, l3, r11, l4, r14, r15, r16, l6, r19]
  · omega_using [c4b, b0, b1, r14, r15, r16, l6, r19]

/-! ## The final reduction -/

/-- `normalize` and `plus5`: the limbs `h1, h2, h3` normalized (carrying into
`t4`), `g = h + 5` with carries, whose carry out `b` is 1 iff `g ≥ 2¹³⁰`:
then `g - 2¹³⁰` (the limbs `g0, …, g4`) is `h mod p`, and otherwise `h` is. -/
theorem reduce_arith {h0 h1 h2 h3 h4 n1 t2 n2 t3 n3 t4 u0 g0 u1 g1 u2 g2 u3 g3 u4 g4 b : Nat}
    (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 27) (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 26) (b4 : h4 < 2 ^ 26)
    (e1 : n1 = h1 % 2 ^ 26) (e2 : t2 = (h2 + h1 / 2 ^ 26) % 2 ^ 64)
    (e3 : n2 = t2 % 2 ^ 26) (e4 : t3 = (h3 + t2 / 2 ^ 26) % 2 ^ 64)
    (e5 : n3 = t3 % 2 ^ 26) (e6 : t4 = (h4 + t3 / 2 ^ 26) % 2 ^ 64)
    (f0 : u0 = (h0 + 5) % 2 ^ 64) (f1 : g0 = u0 % 2 ^ 26) (f2 : u1 = (n1 + u0 / 2 ^ 26) % 2 ^ 64)
    (f3 : g1 = u1 % 2 ^ 26) (f4 : u2 = (n2 + u1 / 2 ^ 26) % 2 ^ 64)
    (f5 : g2 = u2 % 2 ^ 26) (f6 : u3 = (n3 + u2 / 2 ^ 26) % 2 ^ 64)
    (f7 : g3 = u3 % 2 ^ 26) (f8 : u4 = (t4 + u3 / 2 ^ 26) % 2 ^ 64)
    (f9 : g4 = u4 % 2 ^ 26) (f10 : b = u4 / 2 ^ 26) :
    (b = 1 ∧ val5 g0 g1 g2 g3 g4 = val5 h0 h1 h2 h3 h4 % P ∧
        g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26) ∨
      (b = 0 ∧ val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 % P ∧
        h0 < 2 ^ 26 ∧ n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 < 2 ^ 26) := by
  have hP : P = 2 ^ 130 - 5 := rfl
  obtain ⟨k1, m1⟩ := dm26 (x := h1) rfl e1
  generalize h1 / 2 ^ 26 = a1 at k1 e2
  have A1 : a1 < 2 := by omega_using [b1, k1]
  have ht2 := mod64 e2 (by omega_using [b2, A1])
  obtain ⟨k2, m2⟩ := dm26 (x := t2) rfl e3
  generalize t2 / 2 ^ 26 = a2 at k2 e4
  have A2 : a2 < 2 := by omega_using [b2, A1, ht2, k2]
  have ht3 := mod64 e4 (by omega_using [b3, A2])
  obtain ⟨k3, m3⟩ := dm26 (x := t3) rfl e5
  generalize t3 / 2 ^ 26 = a3 at k3 e6
  have A3 : a3 < 2 := by omega_using [b3, A2, ht3, k3]
  have ht4 := mod64 e6 (by omega_using [b4, A3])
  have hn : n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 ≤ 2 ^ 26 :=
    ⟨m1, m2, m3, by omega_using [b4, A3, ht4]⟩
  have hu0 := mod64 f0 (by omega_using [b0])
  obtain ⟨k4, m4⟩ := dm26 (x := u0) rfl f1
  generalize u0 / 2 ^ 26 = a4 at k4 f2
  have A4 : a4 < 2 := by omega_using [b0, hu0, k4]
  have hu1 := mod64 f2 (by omega_using [m1, A4])
  obtain ⟨k5, m5⟩ := dm26 (x := u1) rfl f3
  generalize u1 / 2 ^ 26 = a5 at k5 f4
  have A5 : a5 < 2 := by omega_using [m1, A4, hu1, k5]
  have hu2 := mod64 f4 (by omega_using [m2, A5])
  obtain ⟨k6, m6⟩ := dm26 (x := u2) rfl f5
  generalize u2 / 2 ^ 26 = a6 at k6 f6
  have A6 : a6 < 2 := by omega_using [m2, A5, hu2, k6]
  have hu3 := mod64 f6 (by omega_using [m3, A6])
  obtain ⟨k7, m7⟩ := dm26 (x := u3) rfl f7
  generalize u3 / 2 ^ 26 = a7 at k7 f8
  have A7 : a7 < 2 := by omega_using [m3, A6, hu3, k7]
  have hu4 := mod64 f8 (by omega_using [hn.2.2.2, A7])
  obtain ⟨k8, m8⟩ := dm26 f10 f9
  have hV : val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 := by
    simp only [val5]; omega_using [k1, ht2, k2, ht3, k3, ht4]
  have hG : val5 g0 g1 g2 g3 g4 + 2 ^ 130 * b = val5 h0 n1 n2 n3 t4 + 5 := by
    simp only [val5]; omega_using [k4, k5, k6, k7, k8, hu0, hu1, hu2, hu3, hu4]
  have hg : g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26 :=
    ⟨m4, m5, m6, m7, m8⟩
  have hGl := val5_lt m4 m5 m6 m7 m8
  have hVl := val5_le b0 m1 m2 m3 hn.2.2.2
  rw [← hV]
  generalize val5 g0 g1 g2 g3 g4 = G at hG hGl ⊢
  generalize val5 h0 n1 n2 n3 t4 = V at hG hVl ⊢
  rcases (by omega_using [hn.2.2.2, A7, hu4, k8] : b = 0 ∨ b = 1) with h | h
  · right
    subst h
    have lt : V < P := by rw [hP]; omega_using [hG, hGl]
    exact ⟨rfl, (Nat.mod_eq_of_lt lt).symm, b0, hn.1, hn.2.1, hn.2.2.1, by omega_using [hu4, k8, m8]⟩
  · left
    subst h
    have e : V = G + P := by rw [hP]; omega_using [hG]
    have lt : G < P := by rw [hP]; omega_using [hG, hVl]
    refine ⟨rfl, ?_, hg⟩
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt lt]

/-- `pack`: normalized limbs (but for the last) as 64-bit words. -/
theorem pack_arith {l0 l1 l2 l3 l4 : Nat} (b0 : l0 < 2 ^ 26) (b1 : l1 < 2 ^ 26) (b2 : l2 < 2 ^ 26)
    (b3 : l3 < 2 ^ 26) :
    ((l0 + l1 * 2 ^ 26 % 2 ^ 64) % 2 ^ 64 + l2 * 2 ^ 52 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 % 2 ^ 64 ∧
      ((l2 / 2 ^ 12 + l3 * 2 ^ 14 % 2 ^ 64) % 2 ^ 64 + l4 * 2 ^ 40 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 / 2 ^ 64 % 2 ^ 64 ∧
      l4 / 2 ^ 24 = val5 l0 l1 l2 l3 l4 / 2 ^ 128 := by
  simp only [val5]
  refine ⟨by omega_using [], by omega_using [b0, b1], by omega_using [b0, b1, b2, b3]⟩

/-- Adding limbs `s0, …, s4` to limbs `h0, …, h4` (`addLimbs`), with the
carries propagated up to the last limb (`carryStep` and `normalize`). -/
theorem addCarry_arith {h0 h1 h2 h3 h4 s0 s1 s2 s3 s4 a0 a1 a2 a3 a4 b1 b2 b3 b4 : Nat}
    (hh0 : h0 < 2 ^ 27) (hh1 : h1 < 2 ^ 27) (hh2 : h2 < 2 ^ 27) (hh3 : h3 < 2 ^ 27)
    (hh4 : h4 < 2 ^ 27) (hs0 : s0 < 2 ^ 27) (hs1 : s1 < 2 ^ 27) (hs2 : s2 < 2 ^ 27)
    (hs3 : s3 < 2 ^ 27) (hs4 : s4 < 2 ^ 27)
    (e0 : a0 = (h0 + s0) % 2 ^ 64) (e1 : a1 = (h1 + s1) % 2 ^ 64) (e2 : a2 = (h2 + s2) % 2 ^ 64)
    (e3 : a3 = (h3 + s3) % 2 ^ 64) (e4 : a4 = (h4 + s4) % 2 ^ 64)
    (c1 : b1 = (a1 + a0 / 2 ^ 26) % 2 ^ 64) (c2 : b2 = (a2 + b1 / 2 ^ 26) % 2 ^ 64)
    (c3 : b3 = (a3 + b2 / 2 ^ 26) % 2 ^ 64) (c4 : b4 = (a4 + b3 / 2 ^ 26) % 2 ^ 64) :
    val5 (a0 % 2 ^ 26) (b1 % 2 ^ 26) (b2 % 2 ^ 26) (b3 % 2 ^ 26) b4 =
      val5 h0 h1 h2 h3 h4 + val5 s0 s1 s2 s3 s4 ∧ b4 < 2 ^ 29 := by
  have r0 := mod64 e0 (by omega_using [hh0, hs0])
  have r1 := mod64 e1 (by omega_using [hh1, hs1])
  have r2 := mod64 e2 (by omega_using [hh2, hs2])
  have r3 := mod64 e3 (by omega_using [hh3, hs3])
  have r4 := mod64 e4 (by omega_using [hh4, hs4])
  obtain ⟨k0, m0⟩ := dm26 (x := a0) rfl rfl
  generalize a0 / 2 ^ 26 = z0 at k0 c1
  generalize a0 % 2 ^ 26 = w0 at k0 m0 ⊢
  have Z0 : z0 < 8 := by omega_using [hh0, hs0, r0, k0]
  have q1 := mod64 c1 (by omega_using [hh1, hs1, r1, Z0])
  obtain ⟨k1, m1⟩ := dm26 (x := b1) rfl rfl
  generalize b1 / 2 ^ 26 = z1 at k1 c2
  generalize b1 % 2 ^ 26 = w1 at k1 m1 ⊢
  have Z1 : z1 < 8 := by omega_using [hh1, hs1, r1, Z0, q1, k1]
  have q2 := mod64 c2 (by omega_using [hh2, hs2, r2, Z1])
  obtain ⟨k2, m2⟩ := dm26 (x := b2) rfl rfl
  generalize b2 / 2 ^ 26 = z2 at k2 c3
  generalize b2 % 2 ^ 26 = w2 at k2 m2 ⊢
  have Z2 : z2 < 8 := by omega_using [hh2, hs2, r2, Z1, q2, k2]
  have q3 := mod64 c3 (by omega_using [hh3, hs3, r3, Z2])
  obtain ⟨k3, m3⟩ := dm26 (x := b3) rfl rfl
  generalize b3 / 2 ^ 26 = z3 at k3 c4
  generalize b3 % 2 ^ 26 = w3 at k3 m3 ⊢
  have Z3 : z3 < 8 := by omega_using [hh3, hs3, r3, Z2, q3, k3]
  have q4 := mod64 c4 (by omega_using [hh4, hs4, r4, Z3])
  refine ⟨?_, by omega_using [hh4, hs4, r4, Z3, q4]⟩
  simp only [val5]
  omega_using [r0, r1, r2, r3, r4, k0, q1, k1, q2, k2, q3, k3, q4]

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the steps of the code

Untrusted: everything here is checked by Lean. Each lemma runs a few
instructions symbolically and states their effect on the numbers in the
registers, unconditionally (modulo `2⁶⁴` where the code wraps).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂)
    (h₂ : Keeps rs' s₂ s₃) : Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem not_mem2 {a b c : Reg} (h₁ : a ≠ b) (h₂ : a ≠ c) : a ∉ [b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h₁, h₂⟩

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-! ## Instructions -/

theorem exec_lsl_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp only [exec, Size.bits, h, ↓reduceIte]

theorem exec_madd {sz : Size} {s : State} {d n m a : Reg} :
    exec (.madd sz d n m a) s = some (s.write sz d (s.read sz a + s.read sz n * s.read sz m)) := rfl

theorem exec_mul {sz : Size} {s : State} {d n m : Reg} :
    exec (.mul sz d n m) s = some (s.write sz d (s.read sz n * s.read sz m)) := rfl

theorem write_gpr (s : State) (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write .x d x).gpr r = if r = d then x else s.gpr r := rfl

theorem write_gpr_w (s : State) (d : Reg) (x : BitVec 32) (r : Reg) :
    (s.write .w d x).gpr r = if r = d then x.setWidth 64 else s.gpr r := rfl

/-! ## Numbers -/

/-- The mask `2²⁶ - 1`. -/
abbrev M26 : BitVec 64 := 0x3ffffff

theorem and_mask (a : BitVec 64) : (a &&& M26).toNat = a.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and, show M26.toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsl_toNat (a : BitVec 64) (n : Nat) : (a <<< n).toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem add_toNat (a b : BitVec 64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 :=
  BitVec.toNat_add a b

theorem madd_toNat (a b c : BitVec 64) :
    (a + b * c).toNat = (a.toNat + b.toNat * c.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod]

set_option simprocs false in
/-- `2²⁶ - 1` into `x17`. -/
theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' => s'.gpr .x17 = M26 ∧ Keeps [.x17] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mask, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.write, Size.bits, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, BitVec.ofNat_eq_ofNat, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_eq, Nat.mul_one, ite_false]

set_option simprocs false in
/-- The limbs of `lo + 2⁶⁴ hi` (in `x14, x15`) into `x9`–`x13`. -/
theorem split_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block split) s fun s' =>
      v s' .x9 = lim (v s .x14 + 2 ^ 64 * v s .x15) 0 ∧
      v s' .x10 = lim (v s .x14 + 2 ^ 64 * v s .x15) 1 ∧
      v s' .x11 = lim (v s .x14 + 2 ^ 64 * v s .x15) 2 ∧
      v s' .x12 = lim (v s .x14 + 2 ^ 64 * v s .x15) 3 ∧
      v s' .x13 = lim (v s .x14 + 2 ^ 64 * v s .x15) 4 ∧
      Keeps [.x9, .x10, .x11, .x12, .x13, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [split, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_lsr_x (show 52 < 64 by decide),
    exec_lsr_x (show 14 < 64 by decide), exec_lsr_x (show 40 < 64 by decide),
    exec_lsl_x (show 12 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  obtain ⟨a0, a1, a2, a3, a4⟩ := split_arith (v s .x14) (v s .x15) (s.gpr .x14).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hm, and_mask, ← a0]
  · rw [hm, and_mask, lsr_toNat, ← a1]
  · rw [hm, and_mask, add_toNat, lsr_toNat, lsl_toNat, ← a2]
  · rw [hm, and_mask, lsr_toNat, ← a3]
  · rw [lsr_toNat, ← a4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.2.2.2.2, hr.2.1, hr.1, ite_false]

/-! ## Sums of products -/

/-- The 32-bit word at `[x0 + off]`, as a number. -/
abbrev word (s : State) (off : Nat) : Nat := (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 32).toNat

theorem ldrw_toNat (m : Mem) (a : Addr) : ((m.readW a 32).setWidth 64).toNat = (m.readW a 32).toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (m.readW a 32).isLt (by decide))]

set_option simprocs false in
/-- `d = h · c`, the coefficient `c` loaded into `x14`. -/
theorem mul1_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.x14)
    (ho : off % 4 = 0 ∧ off < 16384) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.ldr .w .x14 .x0 off, .mul .x d h .x14]) s fun s' =>
      v s' d = v s h * word s off % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_w ho hin, exec_mul, v, word, write_gpr, write_gpr_w,
    State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left', hh,
    ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_mul, ldrw_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, write_gpr_w, hr.1, hr.2, ite_false]

set_option simprocs false in
/-- `d += h · c`, the coefficient `c` loaded into `x14`. -/
theorem mac_ok (s : State) {d h : Reg} {off : Nat} (hh : h ≠ Reg.x14)
    (hd' : d ≠ Reg.x14) (ho : off % 4 = 0 ∧ off < 16384)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (mac d h off)) s fun s' =>
      v s' d = (v s d + v s h * word s off) % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  apply WP.of_runBlock
  simp only [mac, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_w ho hin, exec_madd, v, word,
    write_gpr, write_gpr_w, State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left',
    hh, hd', ite_false]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [madd_toNat, ldrw_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, write_gpr_w, hr.1, hr.2, ite_false]

/-- A chain of `mac`s. -/
theorem macs_ok {d : Reg} (L : List (Reg × Nat)) (s : State) (hd : Reg.x14 ≠ d) (hd0 : Reg.x0 ≠ d)
    (hL : ∀ p ∈ L, p.1 ≠ Reg.x14 ∧ p.1 ≠ d ∧ (p.2 % 4 = 0 ∧ p.2 < 16384) ∧
      InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 p.2) 4) :
    WP isa (.block (L.flatMap fun p => mac d p.1 p.2)) s fun s' =>
      v s' d = (v s d + (L.map fun p => v s p.1 * word s p.2).sum) % 2 ^ 64 ∧ Keeps [.x14, d] s s' := by
  induction L generalizing s with
  | nil =>
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (s.gpr d).isLt).symm
  | cons p L ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hL p List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (mac_ok s h1 (Ne.symm hd) h3 h4) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.1 _ (not_mem2 (by decide) hd0)
    have hL' : ∀ q ∈ L, q.1 ≠ Reg.x14 ∧ q.1 ≠ d ∧ (q.2 % 4 = 0 ∧ q.2 < 16384) ∧
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 q.2) 4 := by
      intro q hq
      obtain ⟨g1, g2, g3, g4⟩ := hL q (List.mem_cons_of_mem _ hq)
      exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact g4⟩
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, true_or, or_true, imp_self, implies_true, and_self])⟩
    have hw : (L.map fun q => v s₁ q.1 * word s₁ q.2) = (L.map fun q => v s q.1 * word s q.2) := by
      refine List.map_congr_left fun q hq => ?_
      obtain ⟨g1, g2, -, -⟩ := hL q (List.mem_cons_of_mem _ hq)
      simp only [v, word, x0₁, k₁.2.1, k₁.1 q.1 (not_mem2 g1 g2)]
    rw [e₂, hw, e₁, List.map_cons, List.sum_cons]
    omega_using []


theorem dsum_facts : ∀ k < 5, Reg.x14 ≠ D.getD k .x9 ∧ Reg.x0 ≠ D.getD k .x9 ∧
    (coef k 0 % 4 = 0 ∧ coef k 0 < 16384) ∧ 72 ≤ coef k 0 ∧ coef k 0 + 4 ≤ 108 ∧
    ∀ i < 4, H.getD (i + 1) .x4 ≠ Reg.x14 ∧ H.getD (i + 1) .x4 ≠ D.getD k .x9 ∧
      (coef k (i + 1) % 4 = 0 ∧ coef k (i + 1) < 16384) ∧ 72 ≤ coef k (i + 1) ∧
      coef k (i + 1) + 4 ≤ 108 := by
  decide

/-- `dk = Σ hi · coef k i`. -/
theorem dsum_ok (s : State) {k : Nat} (hk : k < 5)
    (hc : ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (dsum k)) s fun s' =>
      v s' (D.getD k .x9) = (v s .x4 * word s (coef k 0) +
        ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * word s (coef k (i + 1))).sum) % 2 ^ 64 ∧
      Keeps [.x14, D.getD k .x9] s s' := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := dsum_facts k hk
  rw [dsum, show ((List.range 4).flatMap fun i => mac (D.getD k .x9) (H.getD (i + 1) .x4) (coef k (i + 1))) =
      (((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))).flatMap fun p =>
        mac (D.getD k .x9) p.1 p.2) by rw [List.flatMap_map]]
  refine WP.block_append (WP.mono (mul1_ok s (by decide) f3 (hc _ f4 f5)) fun s₁ ⟨e₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.1 _ (not_mem2 (by decide) f2)
  have hL : ∀ p ∈ ((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))),
      p.1 ≠ Reg.x14 ∧ p.1 ≠ D.getD k .x9 ∧ (p.2 % 4 = 0 ∧ p.2 < 16384) ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 p.2) 4 := by
    intro p hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨g1, g2, g3, g4, g5⟩ := f6 i hi
    exact ⟨g1, g2, g3, by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc _ g4 g5⟩
  refine WP.mono (macs_ok _ s₁ f1 f2 hL) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp only [List.getD_eq_getElem?_getD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, true_or, or_true, imp_self, implies_true, and_self])⟩
  have hw : (((List.range 4).map fun i => (H.getD (i + 1) .x4, coef k (i + 1))).map fun p =>
      v s₁ p.1 * word s₁ p.2) = ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * word s (coef k (i + 1))) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨g1, g2, -⟩ := f6 i (List.mem_range.mp hi)
    simp only [Function.comp_apply, v, word, x0₁, k₁.2.1, k₁.1 _ (not_mem2 g1 g2)]
  rw [e₂, hw, e₁, Nat.mod_add_mod]

set_option simprocs false in
/-- The carries of `absorb`, from `d0, …, d4` (in `x9`–`x13`) to the new limbs (in `x4`–`x8`). -/
theorem carry_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block carry) s fun s' =>
      (v s .x9 < 2 ^ 60 → v s .x10 < 2 ^ 60 → v s .x11 < 2 ^ 60 → v s .x12 < 2 ^ 60 →
        v s .x13 < 2 ^ 60 →
        val5 (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8) % Spec.Poly1305.P =
          val5 (v s .x9) (v s .x10) (v s .x11) (v s .x12) (v s .x13) % Spec.Poly1305.P ∧
        v s' .x4 < 2 ^ 26 ∧ v s' .x5 < 2 ^ 27 ∧ v s' .x6 < 2 ^ 26 ∧ v s' .x7 < 2 ^ 26 ∧
        v s' .x8 < 2 ^ 26) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [carry, carryStep, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_lsl_x (show 2 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, lsl_toNat]
    obtain ⟨e, c0, c1, c2, c3, c4⟩ := carry_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
    refine ⟨?_, c0, c1, c2, c3, c4⟩
    rw [← e, Nat.add_mul_mod_self_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, hr.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.1, ite_false]

set_option simprocs false in
/-- The two words at `[n + off]` into `x14, x15`. -/
theorem load2_ok (s : State) {n : Reg} {off : Nat} (hn : n ≠ Reg.x14)
    (ho : off % 8 = 0 ∧ off < 32768) (ho' : (off + 8) % 8 = 0 ∧ off + 8 < 32768)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 (off + 8)) 8) :
    WP isa (.block (load2 n off)) s fun s' =>
      s'.gpr .x14 = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      s'.gpr .x15 = s.mem.readW (s.gpr n + BitVec.ofNat 64 (off + 8)) 64 ∧ Keeps [.x14, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [load2, runBlock_cons, runStep_some,
    exec_ldr_x ho h0, State.write, Size.bits, BitVec.setWidth_eq]
  rw [exec_ldr_x ho' (by simpa only [hn, ite_false] using h8)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, State.write, Size.bits,
    BitVec.setWidth_eq, hn, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2, hr.1, ite_false]

set_option simprocs false in
/-- `hi += xi`. -/
theorem addLimbs_ok (s : State) :
    WP isa (.block addLimbs) s fun s' =>
      v s' .x4 = (v s .x4 + v s .x9) % 2 ^ 64 ∧ v s' .x5 = (v s .x5 + v s .x10) % 2 ^ 64 ∧
      v s' .x6 = (v s .x6 + v s .x11) % 2 ^ 64 ∧ v s' .x7 = (v s .x7 + v s .x12) % 2 ^ 64 ∧
      v s' .x8 = (v s .x8 + v s .x13) % 2 ^ 64 ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    v, State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, add_toNat _ _, fun r hr => ?_,
    rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false]

set_option simprocs false in
/-- `h += 2¹²⁸`. -/
theorem padBit_ok (s : State) :
    WP isa (.block padBit) s fun s' =>
      v s' .x8 = (v s .x8 + 2 ^ 24) % 2 ^ 64 ∧ Keeps [.x8, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [padBit, runBlock_cons, runStep_some, runBlock_nil,
    exec, v, State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, BitVec.ofNat_eq_ofNat, Nat.mul_one, hr.2, ite_false]

theorem ofNat_toNat5 : (BitVec.ofNat 64 5).toNat = 5 := rfl
theorem ofNat_toNat1 : (BitVec.ofNat 64 1).toNat = 1 := rfl

theorem sub_toNat (a b : BitVec 64) : (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 :=
  BitVec.toNat_sub a b

/-- Normalized limbs of `h mod p`. -/
def Norm (V a0 a1 a2 a3 a4 : Nat) : Prop :=
  val5 a0 a1 a2 a3 a4 = V % Spec.Poly1305.P ∧
    a0 < 2 ^ 26 ∧ a1 < 2 ^ 26 ∧ a2 < 2 ^ 26 ∧ a3 < 2 ^ 26 ∧ a4 < 2 ^ 26

set_option simprocs false in
/-- `normalize` and `plus5`: the mask in `x14` is zero if the limbs of `h mod p` are
`x9`–`x13`, all ones if they are `x4`–`x8`. -/
theorem reduceA_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block (normalize ++ plus5)) s fun s' =>
      (v s .x4 < 2 ^ 26 → v s .x5 < 2 ^ 27 → v s .x6 < 2 ^ 26 → v s .x7 < 2 ^ 26 → v s .x8 < 2 ^ 26 →
        (v s' .x14 = 0 ∧
          Norm (val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8))
            (v s' .x9) (v s' .x10) (v s' .x11) (v s' .x12) (v s' .x13)) ∨
        (v s' .x14 = 2 ^ 64 - 1 ∧
          Norm (val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8))
            (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8))) ∧
      Keeps [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [normalize, plus5, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_add, exec_addImm_x (show 5 < 4096 by decide),
    exec_subImm_x (show 1 < 4096 by decide), v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat, sub_toNat, ofNat_toNat5, ofNat_toNat1]
    rcases reduce_arith b0 b1 b2 b3 b4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl with ⟨hb, e, g⟩ | ⟨hb, e, g⟩
    · left
      rw [hb]
      exact ⟨rfl, e, g⟩
    · right
      rw [hb]
      exact ⟨rfl, e, g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false]

set_option simprocs false in
/-- Selecting `x9`–`x13` over `x4`–`x8` where the mask `x14` is set. -/
theorem select_ok (s : State) :
    WP isa (.block select) s fun s' =>
      s'.gpr .x4 = s.gpr .x9 ^^^ ((s.gpr .x4 ^^^ s.gpr .x9) &&& s.gpr .x14) ∧
      s'.gpr .x5 = s.gpr .x10 ^^^ ((s.gpr .x5 ^^^ s.gpr .x10) &&& s.gpr .x14) ∧
      s'.gpr .x6 = s.gpr .x11 ^^^ ((s.gpr .x6 ^^^ s.gpr .x11) &&& s.gpr .x14) ∧
      s'.gpr .x7 = s.gpr .x12 ^^^ ((s.gpr .x7 ^^^ s.gpr .x12) &&& s.gpr .x14) ∧
      s'.gpr .x8 = s.gpr .x13 ^^^ ((s.gpr .x8 ^^^ s.gpr .x13) &&& s.gpr .x14) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x15] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [select, selectLimb, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2.2.1, hr.2.2.2.2.2, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, ite_false]

theorem select_zero (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& 0) = g := by simp only [BitVec.ofNat_eq_ofNat, BitVec.and_zero, BitVec.xor_zero]
theorem select_ones (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& BitVec.allOnes 64) = h := by
  rw [BitVec.and_allOnes, BitVec.xor_comm h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem eq_zero_of_toNat {a : BitVec 64} (h : a.toNat = 0) : a = 0 := BitVec.eq_of_toNat_eq h
theorem eq_ones_of_toNat {a : BitVec 64} (h : a.toNat = 2 ^ 64 - 1) : a = BitVec.allOnes 64 :=
  BitVec.eq_of_toNat_eq (by rw [h]; rfl)

set_option simprocs false in
/-- The limbs `x4`–`x8` packed into the words `x14, x15, x16`. -/
theorem pack_ok (s : State) :
    WP isa (.block pack) s fun s' =>
      (v s .x4 < 2 ^ 26 → v s .x5 < 2 ^ 26 → v s .x6 < 2 ^ 26 → v s .x7 < 2 ^ 26 →
        v s' .x14 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) % 2 ^ 64 ∧
        v s' .x15 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) / 2 ^ 64 % 2 ^ 64 ∧
        v s' .x16 = val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) / 2 ^ 128) ∧
      Keeps [.x9, .x14, .x15, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [pack, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl_x (show 26 < 64 by decide), exec_lsl_x (show 52 < 64 by decide),
    exec_lsl_x (show 14 < 64 by decide), exec_lsl_x (show 40 < 64 by decide),
    exec_lsr_x (show 12 < 64 by decide), exec_lsr_x (show 24 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [lsr_toNat, add_toNat, lsl_toNat]
    exact pack_arith b0 b1 b2 b3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2, hr.2.2.1, hr.1, hr.2.1, ite_false]

set_option simprocs false in
/-- `hi += xi`, with the carries propagated up to `h4`. -/
theorem addCarry_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block (addLimbs ++ carryStep .x4 .x4 .x5 ++ normalize)) s fun s' =>
      (v s .x4 < 2 ^ 27 → v s .x5 < 2 ^ 27 → v s .x6 < 2 ^ 27 → v s .x7 < 2 ^ 27 → v s .x8 < 2 ^ 27 →
        v s .x9 < 2 ^ 27 → v s .x10 < 2 ^ 27 → v s .x11 < 2 ^ 27 → v s .x12 < 2 ^ 27 →
        v s .x13 < 2 ^ 27 →
        val5 (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8) =
          val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8) +
            val5 (v s .x9) (v s .x10) (v s .x11) (v s .x12) (v s .x13) ∧
        v s' .x4 < 2 ^ 26 ∧ v s' .x5 < 2 ^ 26 ∧ v s' .x6 < 2 ^ 26 ∧ v s' .x7 < 2 ^ 26 ∧
        v s' .x8 < 2 ^ 29) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x14] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addLimbs, normalize, carryStep, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec_logic,
    exec_lsr_x (show 26 < 64 by decide), exec_add, v,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hm, and_mask, lsr_toNat, add_toNat]
    obtain ⟨e, g⟩ := addCarry_arith b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    exact ⟨e, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
      Nat.mod_lt _ (by decide), g⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2, hr.2.2.1, hr.2.1, hr.1, ite_false]

end VG.Proof.Poly1305.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Setup`.
section

section

/-!
# Poly1305 on AArch64: absorbing a block

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- The coefficient of `hi` in `dk`: `r(k-i)` or `5 r(k+5-i)`, for the limbs of `R`. -/
def cval (R k i : Nat) : Nat := if i ≤ k then lim R (k - i) else 5 * lim R (k + 5 - i)

/-- The coefficients stored in the state at `st`, for the clamped `R`. -/
def Coefs (m : Mem) (st : Addr) (R : Nat) : Prop :=
  ∀ k < 5, ∀ i < 5, (m.readW (st + BitVec.ofNat 64 (coef k i)) 32).toNat = cval R k i

/-- The coefficient words may be read. -/
def CoefIn (s : State) : Prop :=
  ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4

/-- `dk`, from the limbs of `h` in `s`. -/
def dform (s : State) (R k : Nat) : Nat :=
  v s .x4 * cval R k 0 + ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * cval R k (i + 1)).sum

theorem dreg_facts : ∀ k < 5, ∀ j < 5, j ≠ k → D.getD j .x9 ≠ D.getD k .x9 ∧ D.getD j .x9 ≠ .x14 := by
  decide

theorem hreg_facts : ∀ i < 5, H.getD i .x4 ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14] := by decide +kernel

theorem dreg_mem : ∀ n < 5, D.getD n .x9 ∈ [Reg.x9, .x10, .x11, .x12, .x13, .x14] := by decide +kernel

theorem prods_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s) :
    ∀ n ≤ 5, WP isa (.block ((List.range n).flatMap dsum)) s fun s' =>
      (∀ k < n, v s' (D.getD k .x9) = dform s R k % 2 ^ 64) ∧
      Keeps [.x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun k hk => absurd hk (by omega_using [hk]), Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hn])) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.gpr'
    have hc₁ : CoefIn s₁ := fun off h₁ h₂ => by
      rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc off h₁ h₂
    refine WP.mono (dsum_ok s₁ (by omega_using [hn]) hc₁) fun s₂ ⟨e₂, k₂⟩ => ⟨fun k hk => ?_, ?_⟩
    · have hH : ∀ i < 5, v s₁ (H.getD i .x4) = v s (H.getD i .x4) := fun i hi => by
        simp only [v]
        rw [k₁.1 _ (hreg_facts i hi)]
      have hW : ∀ i < 5, word s₁ (coef n i) = cval R n i := fun i hi => by
        simp only [word, x0₁, k₁.2.1]; exact hco n (by omega_using [hn]) i hi
      by_cases hkn : k = n
      · subst hkn
        have h0 : v s₁ .x4 = v s .x4 := hH 0 (by decide)
        have hs : ((List.range 4).map fun i => v s₁ (H.getD (i + 1) .x4) * word s₁ (coef k (i + 1))) =
            ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * cval R k (i + 1)) := by
          refine List.map_congr_left fun i hi => ?_
          have hi := List.mem_range.mp hi
          rw [hW (i + 1) (by omega_using [hi]), hH (i + 1) (by omega_using [hi])]
        rw [e₂, hW 0 (by decide), h0, hs, dform]
      · obtain ⟨g1, g2⟩ := dreg_facts n (by omega_using [hn]) k (by omega_using [hn, hk]) hkn
        rw [show v s₂ (D.getD k .x9) = v s₁ (D.getD k .x9) by
          simp only [v]; rw [k₂.1 _ (not_mem2 g2 g1)]]
        exact e₁ k (by omega_using [hk, hkn])
    · refine (k₁.trans k₂).mono fun r hr => ?_
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]
        · exact dreg_mem n (by omega_using [hn])

section
variable (s : State) (R : Nat)
theorem dform0 : dform s R 0 = v s .x4 * lim R 0 + (v s .x5 * (5 * lim R 4) +
    (v s .x6 * (5 * lim R 3) + (v s .x7 * (5 * lim R 2) + (v s .x8 * (5 * lim R 1) + 0)))) := rfl
theorem dform1 : dform s R 1 = v s .x4 * lim R 1 + (v s .x5 * lim R 0 +
    (v s .x6 * (5 * lim R 4) + (v s .x7 * (5 * lim R 3) + (v s .x8 * (5 * lim R 2) + 0)))) := rfl
theorem dform2 : dform s R 2 = v s .x4 * lim R 2 + (v s .x5 * lim R 1 +
    (v s .x6 * lim R 0 + (v s .x7 * (5 * lim R 4) + (v s .x8 * (5 * lim R 3) + 0)))) := rfl
theorem dform3 : dform s R 3 = v s .x4 * lim R 3 + (v s .x5 * lim R 2 +
    (v s .x6 * lim R 1 + (v s .x7 * lim R 0 + (v s .x8 * (5 * lim R 4) + 0)))) := rfl
theorem dform4 : dform s R 4 = v s .x4 * lim R 4 + (v s .x5 * lim R 3 +
    (v s .x6 * lim R 2 + (v s .x7 * lim R 1 + (v s .x8 * lim R 0 + 0)))) := rfl
end

theorem products_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s) :
    WP isa (.block products) s fun s' =>
      v s' .x9 = dform s R 0 % 2 ^ 64 ∧ v s' .x10 = dform s R 1 % 2 ^ 64 ∧
      v s' .x11 = dform s R 2 % 2 ^ 64 ∧ v s' .x12 = dform s R 3 % 2 ^ 64 ∧
      v s' .x13 = dform s R 4 % 2 ^ 64 ∧ Keeps [.x9, .x10, .x11, .x12, .x13, .x14] s s' :=
  WP.mono (prods_ok s R hco hc 5 (Nat.le_refl _)) fun _ ⟨e, k⟩ =>
    ⟨e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), k⟩

/-- `h += 2¹²⁸` if `pad`. -/
theorem padOpt_ok (s : State) (pad : Bool) :
    WP isa (.block (if pad then padBit else [])) s fun s' =>
      v s' .x8 = (v s .x8 + 2 ^ 24 * pad.toNat) % 2 ^ 64 ∧ Keeps [.x8, .x16] s s' := by
  cases pad
  · show WP isa (.block []) s _
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, v]
    exact (Nat.mod_eq_of_lt (s.gpr .x8).isLt).symm
  · show WP isa (.block padBit) s _
    exact WP.mono (padBit_ok s) fun s' ⟨e, k⟩ => ⟨by rw [e]; rfl, k⟩

/-- The limbs of `h` between blocks. -/
def Bounds (s : State) : Prop :=
  v s .x4 < 2 ^ 26 ∧ v s .x5 < 2 ^ 27 ∧ v s .x6 < 2 ^ 26 ∧ v s .x7 < 2 ^ 26 ∧ v s .x8 < 2 ^ 26

/-- `h`, from its limbs. -/
abbrev hv (s : State) : Nat := val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8)

/-- The registers `absorb` writes. -/
abbrev absorbRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16]

/-- The 64-bit word at `p + d`, as a number. -/
abbrev w64 (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

theorem absorb_eq (pad : Bool) : absorb pad = load2 .x1 0 ++ (split ++ (addLimbs ++
    ((if pad then padBit else []) ++ (products ++ carry)))) := by
  simp only [absorb, addBlock, List.append_assoc]

/-- Absorbing the block at `x1`: from `h` within `Bounds`, the new `h` is
congruent to `(h + m + pad · 2¹²⁸) R` modulo `p`, and within `Bounds`. -/
theorem absorb_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .x17 = M26)
    (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (0 + 8)) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  rw [absorb_eq]
  refine WP.block_append (WP.mono (load2_ok s (by decide) (by decide) (by decide) h0 h8)
    fun s₁ ⟨l1, l2, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₁ (by rw [k₁.gpr']; exact hm))
    fun s₂ ⟨m0, m1, m2, m3, m4, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (addLimbs_ok s₂) fun s₃ ⟨a0, a1, a2, a3, a4, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (padOpt_ok s₃ pad) fun s₄ ⟨p4, k₄⟩ => ?_)
  have k₁₄ := ((k₁.trans k₂).trans k₃).trans k₄
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := k₁₄.gpr'
  refine WP.block_append (WP.mono (products_ok s₄ R (by rw [k₁₄.2.1, x0₄]; exact hco)
    (fun off h₁ h₂ => by rw [k₁₄.2.2.1, k₁₄.2.2.2, x0₄]; exact hc off h₁ h₂))
    fun s₅ ⟨d0, d1, d2, d3, d4, k₅⟩ => ?_)
  refine WP.mono (carry_ok s₅ (by rw [(k₁₄.trans k₅).gpr']; exact hm)) fun s₆ ⟨hcar, k₆⟩ => ?_
  refine ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_, (((k₁₄.trans k₅).trans k₆).mono (by decide))⟩
  -- The block, as a number `N`, and its limbs.
  have hN := val5_lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15)
  have hNlt : v s₁ .x14 + 2 ^ 64 * v s₁ .x15 < 2 ^ 128 := by
    have := (s₁.gpr .x14).isLt; have := (s₁.gpr .x15).isLt; simp only [v]; omega
  have n0 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 0) (by decide)
  have n1 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 1) (by decide)
  have n2 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 2) (by decide)
  have n3 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 3) (by decide)
  have n4 := lim4_lt hNlt
  -- `h + m` in `s₄`.
  have h4₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s₂ r = v s r := fun r hr => by
    simp only [v]; rw [k₂.1 r (by revert hr; decide +revert), k₁.1 r (by revert hr; decide +revert)]
  have hp : pad.toNat ≤ 1 := by cases pad <;> decide
  rw [h4₂ .x4 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), m0] at a0; rw [h4₂ .x5 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m1] at a1
  rw [h4₂ .x6 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m2] at a2; rw [h4₂ .x7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m3] at a3
  rw [h4₂ .x8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), m4] at a4
  have e0 : v s₄ .x4 = v s .x4 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 0 := by
    rw [show v s₄ .x4 = v s₃ .x4 by simp only [v]; rw [k₄.gpr'], a0]; omega_using [b0, n0]
  have e1 : v s₄ .x5 = v s .x5 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 1 := by
    rw [show v s₄ .x5 = v s₃ .x5 by simp only [v]; rw [k₄.gpr'], a1]; omega_using [b1, n1]
  have e2 : v s₄ .x6 = v s .x6 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 2 := by
    rw [show v s₄ .x6 = v s₃ .x6 by simp only [v]; rw [k₄.gpr'], a2]; omega_using [b2, n2]
  have e3 : v s₄ .x7 = v s .x7 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 3 := by
    rw [show v s₄ .x7 = v s₃ .x7 by simp only [v]; rw [k₄.gpr'], a3]; omega_using [b3, n3]
  have e4 : v s₄ .x8 = v s .x8 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 4 + 2 ^ 24 * pad.toNat := by
    rw [p4, a4]; omega_using [b4, n4, hp]
  -- The sums of products.
  obtain ⟨q0, q1, q2, q3, q4, hq⟩ := dsum_arith (a0 := v s₄ .x4) (a1 := v s₄ .x5) (a2 := v s₄ .x6)
    (a3 := v s₄ .x7) (a4 := v s₄ .x8) (by omega_using [e0, b0, n0]) (by omega_using [e1, b1, n1])
    (by omega_using [e2, b2, n2]) (by omega_using [e3, b3, n3]) (by omega_using [e4, b4, n4, hp]) hR
  rw [dform0] at d0; rw [dform1] at d1; rw [dform2] at d2; rw [dform3] at d3; rw [dform4] at d4
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q0 (by decide))] at d0
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q1 (by decide))] at d1
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q2 (by decide))] at d2
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q3 (by decide))] at d3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q4 (by decide))] at d4
  obtain ⟨hv₆, c0, c1, c2, c3, c4⟩ := hcar (by rw [d0]; exact q0) (by rw [d1]; exact q1)
    (by rw [d2]; exact q2) (by rw [d3]; exact q3) (by rw [d4]; exact q4)
  refine ⟨?_, c0, c1, c2, c3, c4⟩
  rw [hv, hv₆, d0, d1, d2, d3, d4, hq]
  have hw : w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 =
      v s₁ .x14 + 2 ^ 64 * v s₁ .x15 := by
    simp only [v, w64, l1, l2]
  have ha : val5 (v s₄ .x4) (v s₄ .x5) (v s₄ .x6) (v s₄ .x7) (v s₄ .x8) =
      hv s + (w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 + 2 ^ 128 * pad.toNat) := by
    rw [hw, ← hN]
    simp only [hv, val5, e0, e1, e2, e3, e4]
    omega_using []
  rw [ha]

end VG.Proof.Poly1305.AArch64

end

section

/-!
# Poly1305 on AArch64: the final reduction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- `h` reduced fully, into normalized limbs. -/
theorem reduce_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block reduce) s fun s' =>
      (Bounds s → Norm (hv s) (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s s' := by
  rw [reduce]
  refine WP.block_append (WP.mono (reduceA_ok s hm) fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.mono (select_ok s₁) fun s₂ ⟨c4, c5, c6, c7, c8, k₂⟩ => ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_,
    (k₁.trans k₂).mono (by decide)⟩
  rcases h₁ b0 b1 b2 b3 b4 with ⟨hz, hn⟩ | ⟨ho, hn⟩
  · have hz := eq_zero_of_toNat hz
    simp only [v, c4, c5, c6, c7, c8, hz, select_zero]
    exact hn
  · have ho := eq_ones_of_toNat ho
    simp only [v, c4, c5, c6, c7, c8, ho, select_ones]
    exact hn

end VG.Proof.Poly1305.AArch64

end

section

/-!
# Poly1305 on AArch64: the state in memory

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by decide) (by decide) h) (by decide)

theorem readW32_writeW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  Mem.readW_writeW_sep (sep_off p hd he (by decide) (by decide) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) :=
  Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff]) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 :=
  contains_off h (by omega_using [h])

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = w64 m st 0 + 2 ^ 64 * w64 m st 8 + 2 ^ 128 * w64 m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, w64, add_ofNat_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w64 m p 0 + 2 ^ 64 * w64 m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, w64, add_ofNat_zero]
  rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, w64, w64, off, add_ofNat_zero, add_ofNat_add, Poly1305.clamp_words]

theorem Rk_lt (m : Mem) (st : Addr) : Rk m st < 2 ^ 128 := by
  have := (m.readW (off st 24) 64 &&& M0).isLt
  have := (m.readW (off st 32) 64 &&& M1).isLt
  simp only [Rk]
  omega

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the coefficients and the accumulator on entry

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

set_option simprocs false in
/-- `r` clamped. -/
theorem clampR_ok (s : State) :
    WP isa (.block clampR) s fun s' =>
      s'.gpr .x14 = s.gpr .x14 &&& M0 ∧ s'.gpr .x15 = s.gpr .x15 &&& M1 ∧
      Keeps [.x14, .x15, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [clampR, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [movz_movk64']
  · rw [movz_movk64']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.1, BitVec.ofNat_eq_ofNat, Nat.mul_zero, BitVec.shiftLeft_zero, Nat.mul_one, hr.2.2, hr.1, ite_false]

set_option simprocs false in
/-- `sj = 5 rj`. -/
theorem times5_ok (s : State) :
    WP isa (.block times5) s fun s' =>
      v s' .x4 = (v s .x10 * 2 ^ 2 % 2 ^ 64 + v s .x10) % 2 ^ 64 ∧
      v s' .x5 = (v s .x11 * 2 ^ 2 % 2 ^ 64 + v s .x11) % 2 ^ 64 ∧
      v s' .x6 = (v s .x12 * 2 ^ 2 % 2 ^ 64 + v s .x12) % 2 ^ 64 ∧
      v s' .x7 = (v s .x13 * 2 ^ 2 % 2 ^ 64 + v s .x13) % 2 ^ 64 ∧
      Keeps [.x4, .x5, .x6, .x7] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [times5, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl_x (show 2 < 64 by decide), exec_add, v, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩ <;> try rw [add_toNat, lsl_toNat]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2, hr.2.2.1, hr.2.1, hr.1, ite_false]

/-- The memory after the coefficients are stored: `r j` at `rOff j`, `s j` at `sOff j`. -/
def coefMem (m : Mem) (st : Addr) (r s : Nat → BitVec 64) : Mem :=
  ((((((((m.writeW (off st (rOff 0)) ((r 0).setWidth 32)).writeW (off st (rOff 1))
    ((r 1).setWidth 32)).writeW (off st (rOff 2)) ((r 2).setWidth 32)).writeW (off st (rOff 3))
    ((r 3).setWidth 32)).writeW (off st (rOff 4)) ((r 4).setWidth 32)).writeW (off st (sOff 1))
    ((s 1).setWidth 32)).writeW (off st (sOff 2)) ((s 2).setWidth 32)).writeW (off st (sOff 3))
    ((s 3).setWidth 32)).writeW (off st (sOff 4)) ((s 4).setWidth 32)

/-- The registers holding `rj` and `sj` when they are stored. -/
def rv (s : State) (j : Nat) : BitVec 64 := s.gpr (D.getD j .x9)
def sv (s : State) (j : Nat) : BitVec 64 := s.gpr (H.getD (j - 1) .x4)

set_option simprocs false in
theorem storeCoefs_ok (s : State)
    (hw : ∀ d, 72 ≤ d → d + 4 ≤ 108 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 4) :
    WP isa (.block storeCoefs) s fun s' =>
      s'.mem = coefMem s.mem (s.gpr .x0) (rv s) (sv s) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have o0 := hw (72 + 4 * 0) (by decide) (by decide); have o1 := hw (72 + 4 * 1) (by decide) (by decide)
  have o2 := hw (72 + 4 * 2) (by decide) (by decide); have o3 := hw (72 + 4 * 3) (by decide) (by decide)
  have o4 := hw (72 + 4 * 4) (by decide) (by decide); have o5 := hw (88 + 4 * 1) (by decide) (by decide)
  have o6 := hw (88 + 4 * 2) (by decide) (by decide); have o7 := hw (88 + 4 * 3) (by decide) (by decide)
  have o8 := hw (88 + 4 * 4) (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeCoefs, rOff, sOff, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, Size.bytes, State.store, State.read, Size.bits, Option.bind_some,
    o0, o1, o2, o3, o4, o5, o6, o7, o8, ite_true, Option.some.injEq, exists_eq_left']
  trivial

set_option simprocs false in
theorem coefMem_r (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj : j < 5) :
    (coefMem m st r s).readW (off st (rOff j)) 32 = (r j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj]
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

set_option simprocs false in
theorem coefMem_s (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj₁ : 1 ≤ j) (hj : j < 5) :
    (coefMem m st r s).readW (off st (sOff j)) 32 = (s j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj₁, hj]
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

/-- The coefficients' region. -/
abbrev cR (st : Addr) : Region := ⟨off st 72, 36⟩

theorem coefMem_frame (m : Mem) (st : Addr) (r s : Nat → BitVec 64) :
    Frame [cR st] m (coefMem m st r s) := by
  have c : ∀ d, 72 ≤ d → d + 4 ≤ 108 → (cR st).Contains (off st d) (32 / 8) := fun d h₁ h₂ => by
    exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)
  simp only [coefMem]
  refine (((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c (rOff 0) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (rOff 2) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (rOff 3) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 4) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (sOff 2) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (sOff 3) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 4) ?_ ?_)
  all_goals decide

/-- The coefficients read back. -/
theorem coefMem_coefs (m : Mem) (st : Addr) (r s : Nat → BitVec 64) (R : Nat)
    (hr : ∀ j < 5, ((r j).setWidth 32).toNat = lim R j)
    (hs : ∀ j, 1 ≤ j → j < 5 → ((s j).setWidth 32).toNat = 5 * lim R j) :
    Coefs (coefMem m st r s) st R := by
  intro k hk i hi
  by_cases h : i ≤ k
  · have e : coef k i = rOff (k - i) := ite_eq_left h
    have e' : cval R k i = lim R (k - i) := ite_eq_left h
    rw [e, e', ← hr (k - i) (by omega_using [hk, hi, h])]
    exact congrArg BitVec.toNat (coefMem_r m st r s (by omega_using [hk, hi, h]))
  · have e : coef k i = sOff (k + 5 - i) := ite_eq_right h
    have e' : cval R k i = 5 * lim R (k + 5 - i) := ite_eq_right h
    rw [e, e', ← hs (k + 5 - i) (by omega_using [hk, hi]) (by omega_using [h])]
    exact congrArg BitVec.toNat (coefMem_s m st r s (by omega_using [hk, hi]) (by omega_using [h]))

set_option simprocs false in
/-- The limbs of the stored `h` into `x4`–`x8`, from those of its low 128 bits in `x9`–`x13`. -/
theorem moveH_ok (s : State) (h16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 8) :
    WP isa (.block moveH) s fun s' =>
      v s' .x4 = v s .x9 ∧ v s' .x5 = v s .x10 ∧ v s' .x6 = v s .x11 ∧ v s' .x7 = v s .x12 ∧
      v s' .x8 = (v s .x13 + w64 s.mem (s.gpr .x0) 16 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [moveH, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldr_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide) h16, exec_lsl_x (show 24 < 64 by decide),
    exec_addImm_x (show 0 < 4096 by decide), exec_add, v, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, add_ofNat_zero, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat, lsl_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, hr.2.2.2.2.2, ite_false]

/-! ## `setup` -/

/-- The registers `setup` writes. -/
abbrev setupRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The state after `setup`, from `s₀`. -/
structure Setup (s₀ s : State) : Prop where
  gpr : ∀ r, r ∉ setupRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mask : s.gpr .x17 = M26
  frame : Frame [cR (s₀.gpr .x0)] s₀.mem s.mem
  coefs : Coefs s.mem (s₀.gpr .x0) (Rk s₀.mem (s₀.gpr .x0))
  acc : leNum (bytesAt s₀.mem (s₀.gpr .x0) 24) < P →
    hv s = leNum (bytesAt s₀.mem (s₀.gpr .x0) 24) ∧ Bounds s

theorem times5_eq {N : Nat} (h : N < 2 ^ 26) : (N * 2 ^ 2 % 2 ^ 64 + N) % 2 ^ 64 = 5 * N := by
  omega_using [h]

theorem lt5_cases {j : Nat} (h : j < 5) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [h]
theorem lt5_cases' {j : Nat} (h₁ : 1 ≤ j) (h : j < 5) : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [h₁, h]

/-- The limbs of `h = W0 + 2⁶⁴ W1 + 2¹²⁸ W2 < p`, as `loadH` computes them. -/
theorem loadH_arith {W0 W1 W2 : Nat} (h0 : W0 < 2 ^ 64) (h1 : W1 < 2 ^ 64)
    (hP : W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 < P) :
    val5 (lim (W0 + 2 ^ 64 * W1) 0) (lim (W0 + 2 ^ 64 * W1) 1) (lim (W0 + 2 ^ 64 * W1) 2)
        (lim (W0 + 2 ^ 64 * W1) 3) ((lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64) =
      W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 ∧
    lim (W0 + 2 ^ 64 * W1) 0 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 1 < 2 ^ 27 ∧
    lim (W0 + 2 ^ 64 * W1) 2 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 3 < 2 ^ 26 ∧
    (lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 < 2 ^ 26 := by
  have e := val5_lim (W0 + 2 ^ 64 * W1)
  have b0 := lim_lt (W0 + 2 ^ 64 * W1) (j := 0) (by decide)
  have b1 := lim_lt (W0 + 2 ^ 64 * W1) (j := 1) (by decide)
  have b2 := lim_lt (W0 + 2 ^ 64 * W1) (j := 2) (by decide)
  have b3 := lim_lt (W0 + 2 ^ 64 * W1) (j := 3) (by decide)
  have b4 := lim4_lt (N := W0 + 2 ^ 64 * W1) (by omega_using [h0, h1, e])
  have hW2 : W2 ≤ 3 := by simp only [P] at hP; omega_using [hP, e]
  generalize lim (W0 + 2 ^ 64 * W1) 0 = a0, lim (W0 + 2 ^ 64 * W1) 1 = a1,
    lim (W0 + 2 ^ 64 * W1) 2 = a2, lim (W0 + 2 ^ 64 * W1) 3 = a3,
    lim (W0 + 2 ^ 64 * W1) 4 = a4 at *
  simp only [val5] at e ⊢
  omega_using [hW2, e, b0, b1, b2, b3, b4]

theorem lt32 {N : Nat} (h : N < 2 ^ 26) : N < 2 ^ 32 := by omega_using [h]

theorem times5_lt {N : Nat} (h : N < 2 ^ 26) : 5 * N < 2 ^ 32 := by omega_using [h]

/-- A coefficient in a register, stored as a 32-bit word. -/
theorem coef_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 32) :
    (x.setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, h, Nat.mod_eq_of_lt hn]

theorem coefMem_readW_low (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {d : Nat} (hd : d + 8 ≤ 56) :
    (coefMem m st r s).readW (off st d) 64 = m.readW (off st d) 64 := by
  refine (coefMem_frame m st r s).readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint st (by omega_using [hd]) (by omega_using [hd]) (by decide)

theorem setup_ok (s₀ : State) (hw : sR (s₀.gpr .x0) ∈ s₀.wr) :
    WP isa (.block setup) s₀ (Setup s₀) := by
  have i : ∀ d n, d + n ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x0) d) n :=
    fun d n h => ⟨_, List.mem_append_right _ hw, contains_off h (by omega_using [h])⟩
  rw [setup, coeffs, loadH]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (mask_ok s₀) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr'
  refine WP.block_append (WP.mono (load2_ok s₁ (n := .x0) (off := 24) (by decide) (by decide)
    (by decide) (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i 24 8 (by decide))
    (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i (24 + 8) 8 (by decide))) fun s₂ ⟨l₁, l₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (clampR_ok s₂) fun s₃ ⟨c₁, c₂, k₃⟩ => ?_)
  have k₁₃ := (k₁.trans k₂).trans k₃
  refine WP.block_append (WP.mono (split_ok s₃ (by rw [(k₂.trans k₃).gpr']; exact m₁))
    fun s₄ ⟨r0, r1, r2, r3, r4, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (times5_ok s₄) fun s₅ ⟨t1, t2, t3, t4, k₅⟩ => ?_)
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  have x0₅ : s₅.gpr .x0 = s₀.gpr .x0 := k₁₅.gpr'
  have m₅ : s₅.gpr .x17 = M26 := by rw [(((k₂.trans k₃).trans k₄).trans k₅).gpr']; exact m₁
  refine WP.block_append (WP.mono (storeCoefs_ok s₅ fun d h₁ h₂ => by
    rw [k₁₅.2.2.2, x0₅]; exact ⟨_, hw, contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩)
    fun s₆ ⟨mm₆, g₆, rd₆, wr₆⟩ => ?_)
  have x0₆ : s₆.gpr .x0 = s₀.gpr .x0 := by rw [g₆, x0₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₁₅.2.2.1]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₁₅.2.2.2]
  refine WP.block_append (WP.mono (load2_ok s₆ (n := .x0) (off := 0) (by decide) (by decide)
    (by decide) (by rw [rd₆', wr₆', x0₆]; exact i 0 8 (by decide))
    (by rw [rd₆', wr₆', x0₆]; exact i (0 + 8) 8 (by decide))) fun s₇ ⟨l₃, l₄, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₇ (by
    rw [k₇.gpr', g₆]; exact m₅))
    fun s₈ ⟨h0, h1, h2, h3, h4, k₈⟩ => ?_)
  have k₇₈ := k₇.trans k₈
  refine WP.mono (moveH_ok s₈ (by
    rw [k₇₈.2.2.1, k₇₈.2.2.2, k₇₈.gpr', rd₆', wr₆', x0₆]; exact i 16 8 (by decide)))
    fun s₉ ⟨e0, e1, e2, e3, e4, k₉⟩ => ?_
  have k₇₉ := k₇₈.trans k₉
  have sub : ∀ r, r ∉ setupRegs → ∀ l : List Reg, (∀ x ∈ l, x ∈ setupRegs) → r ∉ l :=
    fun r hr l hl h => hr (hl r h)
  have mem₉ : s₉.mem = coefMem s₀.mem (s₀.gpr .x0) (rv s₅) (sv s₅) := by
    rw [k₇₉.2.1, mm₆, k₁₅.2.1, x0₅]
  have R_eq : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 = Rk s₀.mem (s₀.gpr .x0) := by
    simp only [v, c₁, c₂, l₁, l₂, x0₁, k₁.2.1]
  have b : ∀ j < 4, lim (Rk s₀.mem (s₀.gpr .x0)) j < 2 ^ 26 := fun j hj => lim_lt _ hj
  have b4 := lim4_lt (Rk_lt s₀.mem (s₀.gpr .x0))
  have v5 : ∀ r ∈ [Reg.x9, .x10, .x11, .x12, .x13], v s₅ r = v s₄ r := fun r hr => by
    simp only [v]; rw [k₅.1 r (by revert hr; decide +revert)]
  have q0 : v s₅ .x9 = lim (Rk s₀.mem (s₀.gpr .x0)) 0 := by rw [v5 .x9 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), r0, R_eq]
  have q1 : v s₅ .x10 = lim (Rk s₀.mem (s₀.gpr .x0)) 1 := by rw [v5 .x10 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r1, R_eq]
  have q2 : v s₅ .x11 = lim (Rk s₀.mem (s₀.gpr .x0)) 2 := by rw [v5 .x11 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r2, R_eq]
  have q3 : v s₅ .x12 = lim (Rk s₀.mem (s₀.gpr .x0)) 3 := by rw [v5 .x12 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r3, R_eq]
  have q4 : v s₅ .x13 = lim (Rk s₀.mem (s₀.gpr .x0)) 4 := by rw [v5 .x13 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), r4, R_eq]
  have p1 : v s₅ .x4 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 1 := by
    rw [t1, ← v5 .x10 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q1, times5_eq (b 1 (by decide))]
  have p2 : v s₅ .x5 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 2 := by
    rw [t2, ← v5 .x11 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q2, times5_eq (b 2 (by decide))]
  have p3 : v s₅ .x6 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 3 := by
    rw [t3, ← v5 .x12 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q3, times5_eq (b 3 (by decide))]
  have p4 : v s₅ .x7 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 4 := by
    rw [t4, ← v5 .x13 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), q4, times5_eq (Nat.lt_trans b4 (by decide))]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun hlt => ?_⟩
  · rw [k₇₉.1 r (sub r hr _ (by decide)), g₆, k₁₅.1 r (sub r hr _ (by decide))]
  · rw [k₇₉.2.2.1, rd₆']
  · rw [k₇₉.2.2.2, wr₆']
  · rw [k₇₉.gpr', g₆]; exact m₅
  · rw [mem₉]; exact coefMem_frame _ _ _ _
  · rw [mem₉]
    refine coefMem_coefs _ _ _ _ _ (fun j hj => ?_) (fun j hj₁ hj => ?_)
    · obtain rfl | rfl | rfl | rfl | rfl := lt5_cases hj
      · exact coef_toNat q0 (lt32 (b 0 (by decide)))
      · exact coef_toNat q1 (lt32 (b 1 (by decide)))
      · exact coef_toNat q2 (lt32 (b 2 (by decide)))
      · exact coef_toNat q3 (lt32 (b 3 (by decide)))
      · exact coef_toNat q4 (lt32 (Nat.lt_trans b4 (by decide)))
    · obtain rfl | rfl | rfl | rfl := lt5_cases' hj₁ hj
      · exact coef_toNat p1 (times5_lt (b 1 (by decide)))
      · exact coef_toNat p2 (times5_lt (b 2 (by decide)))
      · exact coef_toNat p3 (times5_lt (b 3 (by decide)))
      · exact coef_toNat p4 (times5_lt (Nat.lt_trans b4 (by decide)))
  · have hs : ∀ d, d + 8 ≤ 56 → w64 s₈.mem (s₈.gpr .x0) d = w64 s₀.mem (s₀.gpr .x0) d := fun d hd => by
      simp only [w64]
      rw [k₇₈.2.1, k₇₈.gpr', mm₆, k₁₅.2.1, x0₆, x0₅]
      exact congrArg BitVec.toNat (coefMem_readW_low _ _ _ _ hd)
    have w0 : v s₇ .x14 = w64 s₀.mem (s₀.gpr .x0) 0 := by
      simp only [v, l₃]; rw [← hs 0 (by decide), k₇₈.2.1, k₇₈.gpr']
    have w1 : v s₇ .x15 = w64 s₀.mem (s₀.gpr .x0) 8 := by
      simp only [v, l₄]; rw [← hs 8 (by decide), k₇₈.2.1, k₇₈.gpr']
    rw [leNum_acc] at hlt ⊢
    rw [h4, w0, w1] at e4
    rw [hs 16 (by decide)] at e4
    rw [h0, w0, w1] at e0; rw [h1, w0, w1] at e1; rw [h2, w0, w1] at e2; rw [h3, w0, w1] at e3
    simp only [hv, Bounds, e0, e1, e2, e3, e4]
    exact loadH_arith (BitVec.isLt _) (BitVec.isLt _) hlt

end VG.Proof.Poly1305.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Blocks`.
section

/-!
# Poly1305 on AArch64: `blocks`

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let key : Region := ⟨s.gpr .x1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .x0) (bytesAt s.mem (s.gpr .x1) 32) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let blocks : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .x0) key msg →
    Repr s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x1) (16 * (s.gpr .x2).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, …)`:
only `count mod 16`, the number of bytes buffered, matters. The state must be
writable, and it may be permitted to write other regions (which it does
not). -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], …)`:
only `count mod 16`, the number of bytes buffered, matters. The state and
`out` must be writable, and it may be permitted to write other regions
(which it does not). -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let out : Region := ⟨s.gpr .x2, 16⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .x2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Common to `blocks` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .x0
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

/-- The memory `setup` leaves. -/
structure Mem₁ (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [cR (st s₀)] s₀.mem m₁
  coefs : Coefs m₁ (st s₀) (Rn s₀)

theorem cR_sub_wR (st : Addr) : Region.Sub (cR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

theorem cR_sub_sR (st : Addr) : Region.Sub (cR st) (sR st) := sub_sR st (by decide)

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

/-- The key of a state that represents a message, and its clamped `r`. -/
theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

set_option simprocs false in
theorem storeH_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .x0) (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .x0) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  simp only [off] at o0 o8 o16
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeH, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    exec_str_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide), o8, o16, Option.some.injEq, exists_eq_left']
  trivial

theorem storeHm_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') (w0 w1 w2 : BitVec 64) :
    Frame [hR st, wR st] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

set_option simprocs false in
theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, storeHm, readW_writeW_off,
    Mem.readW_writeW_self64]

/-- No instruction of `c` writes a callee-saved register. -/
def Untouched (c : Prog isa) : Prop := ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r

theorem Untouched.of_all {c : Prog isa}
    (h : ((instrs c).all fun i => preserved.all fun r => dstOf i != some r) = true) : Untouched c := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksAArch64.pre s₀) : BPre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- What holds between blocks, after `i` of them, with the memory `m₁` left
by `setup`. -/
structure Common (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  mask : s.gpr .x17 = M26
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ Bounds s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop extends Common s₀ m₁ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_add, Nat.reduceLeDiff]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := hp.nb_lt
  rw [blkAddr, Offset.add_add]
  exact contains_off (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

/-- Block words, in memory the code has written only in the coefficients. -/
theorem blk_word {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m) {i d : Nat} (hi : i < nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 = s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 :=
  hf.readW (hp.blk_contains hi hd) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_bl.symm.sub_right (cR_sub_sR _)) (by decide)

theorem coefIn {s : State} (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CoefIn s := fun off h₁ h₂ => by
  rw [hrd, hwr, hx0, hp.wr]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩

end BPre

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 16 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1 ∧
      Keeps [.x1, .x2] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm_x (show 16 < 4096 by decide), exec_subImm_x (show 1 < 4096 by decide), State.read,
    State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2, hr.1, ite_false]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m)
    {i : Nat} (hi : i < nb s₀) :
    w64 m (blkAddr s₀ i) 0 + 2 ^ 64 * w64 m (blkAddr s₀ i) 8 + 2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [w64]
  rw [hp.blk_word hf hi (by decide), hp.blk_word hf hi (by decide), Poly1305.leNum_append,
    Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

theorem bounds_eq {s s' : State} (h : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], s'.gpr r = s.gpr r) :
    hv s' = hv s ∧ (Bounds s → Bounds s') := by
  have e : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s' r = v s r := fun r hr => by simp only [v, h r hr]
  refine ⟨by simp only [hv, e .x4 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), e .x5 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .x6 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .x7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]),
    e .x8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])], fun hb => ?_⟩
  simp only [Bounds, e .x4 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), e .x5 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .x6 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), e .x7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]),
    e .x8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])]
  exact hb

theorem body_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : LInv s₀ m₁ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ m₁ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ m₁ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.x1, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := absorb_ok s true (Rk_lt _ _) hL.mask (by rw [hL.mem, hL.x0]; exact hm.coefs)
    (hp.coefIn hL.x0 hL.rd hL.wr) (hin 0 (by decide)) (hin (0 + 8) (by decide))
  rw [body]
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : Common s₀ m₁ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .x0), hL.x0]
    · rw [k.gpr' (r := .x17), hL.mask]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := bounds_eq (s := s₁) (s' := s₂) fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.x1, hL.mem, block_value hp hm.frame hi, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .x2), hL.x2, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false], hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with x1 := ?_, x2 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .x1), hL.x1, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]

/-! ## Epilogue -/

theorem words_val (V : Nat) :
    V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64 % 2 ^ 64) + 2 ^ 128 * (V / 2 ^ 128) = V := by omega_using []

theorem Mem₁.frame_wR {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) :
    Frame [hR (st s₀), wR (st s₀)] s₀.mem m₁ :=
  hm.frame.sub fun r hr => ⟨wR (st s₀), by simp only [List.mem_cons, Region.mk.injEq, BitVec.add_right_eq_self, BitVec.reduceEq, Nat.reduceEqDiff, and_self, List.not_mem_nil, or_false, or_true], by
    simp only [List.mem_singleton] at hr; subst hr; exact cR_sub_wR _⟩

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s : State}
    (hc : Common s₀ m₁ (nb s₀) s) :
    WP isa (.block (reduce ++ pack ++ storeH)) s fun s' => Proof.Poly1305.blocksAArch64.post s₀ s' := by
  refine WP.block_append (WP.block_append (WP.mono (reduce_ok s hc.mask) fun s₁ ⟨hr, k₁⟩ =>
    WP.mono (pack_ok s₁) fun s₂ ⟨hp₂, k₂⟩ => ?_))
  have x0₂ : s₂.gpr .x0 = st s₀ := by rw [k₂.gpr', k₁.gpr', hc.x0]
  refine WP.mono (storeH_ok s₂ (by
    rw [k₂.2.2.2, k₁.2.2.2, hc.wr, hp.wr, x0₂]; exact List.mem_singleton_self _))
    fun s₃ ⟨m₃, _, _, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  obtain ⟨hN, n0, n1, n2, n3, -⟩ := hr hb
  obtain ⟨w0, w1, w2⟩ := hp₂ n0 n1 n2 n3
  have mem₂ : s₂.mem = m₁ := by rw [k₂.2.1, k₁.2.1, hc.mem]
  rw [x0₂, mem₂] at m₃
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₃.mem := by
    rw [m₃]; exact storeHm_frame hm.frame_wR _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₃, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    have hV : val5 (v s₁ .x4) (v s₁ .x5) (v s₁ .x6) (v s₁ .x7) (v s₁ .x8) =
        Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (nb s₀)) := by
      rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    change v s₂ .x14 + 2 ^ 64 * v s₂ .x15 + 2 ^ 128 * v s₂ .x16 = _
    rw [w0, w1, w2, words_val, hV]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ (Proof.Poly1305.blocksAArch64.post s₀) := by
  refine WP.seq (WP.mono (setup_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ h₁ => ?_)
  have hm : Mem₁ s₀ s₁.mem := ⟨h₁.frame, h₁.coefs⟩
  have hc₀ : Common s₀ s₁.mem 0 s₁ := ⟨h₁.gpr .x0 (by decide), h₁.mask, h₁.rd, h₁.wr, rfl,
    fun hA => by
      obtain ⟨e, b⟩ := h₁.acc hA
      refine ⟨?_, b⟩
      rw [e, show blks s₀ 0 = [] by simp only [blks, bytesAt, Nat.mul_zero, List.range_zero, List.map_nil], Poly1305.absorbAll_nil]⟩
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := h₁.gpr .x2 (by decide)
  refine WP.seq (WP.mono (Q := Common s₀ s₁.mem (nb s₀)) ?_ fun s₂ hc₂ => epilogue_ok hp hm hc₂)
  refine WP.ite (s₁.read .x .x2 == 0) rfl (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_iff_eq] at h
      simp only [nb, h, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ s₁.mem i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ s₁.mem (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hm hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ s₁.mem 0 s₁ :=
      { hc₀ with
        x1 := by rw [h₁.gpr .x1 (by decide)]; simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]
        x2 := by rw [x2₁]; simp only [nb, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_untouched : Untouched Impl.Poly1305.AArch64.blocks :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (blocks_untouched r hr) he, Exec.sp he⟩, h⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksAArch64.pre
    Proof.Poly1305.blocksAArch64.pub Impl.Poly1305.AArch64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem blocks_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.blocks (Spec.Poly1305.blocksContract AArch64.abi)
      :=
  Verified.of_correct blocks_ok blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksAArch64, AArch64.abi, AArch64.argRegs] [Proof.Poly1305.AArch64.blocksSat]
      using Proof.Poly1305.AArch64.blocksSat)

end VG.Proof.Poly1305.AArch64

end
