import Mathlib.Tactic.Ring
import VerifiedGarbage.Spec.Poly1305

/-!
# Poly1305 on AArch64: the arithmetic in radix `2²⁶`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/AArch64.lean`), as natural numbers: five limbs `a0, …, a4`
stand for `val5 a0 a1 a2 a3 a4 = a0 + 2²⁶ a1 + 2⁵² a2 + 2⁷⁸ a3 + 2¹⁰⁴ a4`.
-/

namespace VG.Proof.Poly1305.AArch64

open VG.Spec.Poly1305 (P)

/-- The number with the limbs `a0, …, a4`. -/
def val5 (a0 a1 a2 a3 a4 : Nat) : Nat := a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4

/-- Limb `j` of `N`: 26 bits, but for the last, which has the rest. -/
def lim (N j : Nat) : Nat := if j < 4 then N / 2 ^ (26 * j) % 2 ^ 26 else N / 2 ^ 104

theorem lim0 (N : Nat) : lim N 0 = N % 2 ^ 26 := by simp [lim]
theorem lim1 (N : Nat) : lim N 1 = N / 2 ^ 26 % 2 ^ 26 := by simp [lim]
theorem lim2 (N : Nat) : lim N 2 = N / 2 ^ 52 % 2 ^ 26 := by simp [lim]
theorem lim3 (N : Nat) : lim N 3 = N / 2 ^ 78 % 2 ^ 26 := by simp [lim]
theorem lim4 (N : Nat) : lim N 4 = N / 2 ^ 104 := by simp [lim]

theorem val5_lim (N : Nat) : val5 (lim N 0) (lim N 1) (lim N 2) (lim N 3) (lim N 4) = N := by
  simp only [val5, lim0, lim1, lim2, lim3, lim4]
  omega

theorem lim_lt (N : Nat) {j : Nat} (hj : j < 4) : lim N j < 2 ^ 26 := by
  simp only [lim, hj, ite_true]
  exact Nat.mod_lt _ (by norm_num)

theorem lim4_lt {N : Nat} (h : N < 2 ^ 128) : lim N 4 < 2 ^ 24 := by
  rw [lim4]; omega

/-- The limbs `split` computes from the words `lo, hi`. -/
theorem split_arith (lo hi : Nat) (hlo : lo < 2 ^ 64) :
    lo % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 0 ∧
    lo / 2 ^ 26 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 1 ∧
    (lo / 2 ^ 52 + hi * 2 ^ 12 % 2 ^ 64) % 2 ^ 64 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 2 ∧
    hi / 2 ^ 14 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 3 ∧
    hi / 2 ^ 40 = lim (lo + 2 ^ 64 * hi) 4 := by
  simp only [lim0, lim1, lim2, lim3, lim4]
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

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
  have hP : P + 5 = 2 ^ 130 := by simp [P]
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
    simp only [val5]; ring
  rw [← hP, Nat.add_mul] at e
  omega

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
  have r0 := lim_lt R (j := 0) (by omega); have r1 := lim_lt R (j := 1) (by omega)
  have r2 := lim_lt R (j := 2) (by omega); have r3 := lim_lt R (j := 3) (by omega)
  have r4 := lt_trans (lim4_lt hR) (show 2 ^ 24 < 2 ^ 26 by norm_num)
  have e := product_identity a0 a1 a2 a3 a4 (lim R 0) (lim R 1) (lim R 2) (lim R 3) (lim R 4)
  rw [val5_lim] at e
  -- Every product is less than `2⁵⁷`.
  have p : ∀ a j, a < 2 ^ 28 → j < 2 ^ 26 → a * j < 2 ^ 57 ∧ a * (5 * j) < 2 ^ 57 := by
    intro a j ha hj
    have h1 := mul_lt' ha hj
    have h2 := mul_lt' ha (show 5 * j < 5 * 2 ^ 26 by omega)
    exact ⟨by norm_num at h1 ⊢; omega, by norm_num at h2 ⊢; omega⟩
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
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
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
  have r2 : d1' = d1 + c0 := by omega
  have r5 : d2' = d2 + c1 := by omega
  have r8 : d3' = d3 + c2 := by omega
  have r11 : d4' = d4 + c2' := by omega
  have r14 : q = c4 * 4 := by omega
  have r15 : c5 = c4 + q := by omega
  have r16 : f = e0 + c5 := by omega
  have r19 : g1 = e1 + c6 := by omega
  subst r2 r5 r8 r11 r14 r15 r16 r19
  simp only [val5, P]
  omega

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
  have ht2 : t2 = h2 + h1 / 2 ^ 26 := by omega
  have ht3 : t3 = h3 + t2 / 2 ^ 26 := by omega
  have ht4 : t4 = h4 + t3 / 2 ^ 26 := by omega
  have hu0 : u0 = h0 + 5 := by omega
  have hu1 : u1 = n1 + u0 / 2 ^ 26 := by omega
  have hu2 : u2 = n2 + u1 / 2 ^ 26 := by omega
  have hu3 : u3 = n3 + u2 / 2 ^ 26 := by omega
  have hu4 : u4 = t4 + u3 / 2 ^ 26 := by omega
  have hV : val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 := by simp only [val5]; omega
  have hG : val5 g0 g1 g2 g3 g4 + 2 ^ 130 * b = val5 h0 n1 n2 n3 t4 + 5 := by simp only [val5]; omega
  rw [← hV]
  have hn : n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 ≤ 2 ^ 26 := by omega
  have hg : g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26 := by omega
  rcases (by omega : b = 0 ∨ b = 1) with h | h
  · right
    subst h
    simp only [val5] at hG
    have lt : val5 h0 n1 n2 n3 t4 < P := by simp only [val5]; rw [hP]; omega
    exact ⟨rfl, (Nat.mod_eq_of_lt lt).symm, b0, hn.1, hn.2.1, hn.2.2.1, by omega⟩
  · left
    subst h
    simp only [val5] at hG
    have ge : P ≤ val5 h0 n1 n2 n3 t4 := by simp only [val5]; rw [hP]; omega
    have lt : val5 h0 n1 n2 n3 t4 - P < P := by simp only [val5]; rw [hP]; omega
    refine ⟨rfl, ?_, hg⟩
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt, hP]
    simp only [val5]
    omega

/-- `pack`: normalized limbs (but for the last) as 64-bit words. -/
theorem pack_arith {l0 l1 l2 l3 l4 : Nat} (b0 : l0 < 2 ^ 26) (b1 : l1 < 2 ^ 26) (b2 : l2 < 2 ^ 26)
    (b3 : l3 < 2 ^ 26) :
    ((l0 + l1 * 2 ^ 26 % 2 ^ 64) % 2 ^ 64 + l2 * 2 ^ 52 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 % 2 ^ 64 ∧
      ((l2 / 2 ^ 12 + l3 * 2 ^ 14 % 2 ^ 64) % 2 ^ 64 + l4 * 2 ^ 40 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 / 2 ^ 64 % 2 ^ 64 ∧
      l4 / 2 ^ 24 = val5 l0 l1 l2 l3 l4 / 2 ^ 128 := by
  simp only [val5]
  refine ⟨by omega, by omega, by omega⟩

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
  have r0 : a0 = h0 + s0 := by omega
  have r1 : a1 = h1 + s1 := by omega
  have r2 : a2 = h2 + s2 := by omega
  have r3 : a3 = h3 + s3 := by omega
  have r4 : a4 = h4 + s4 := by omega
  subst r0 r1 r2 r3 r4
  have q1 : b1 = h1 + s1 + (h0 + s0) / 2 ^ 26 := by omega
  have q2 : b2 = h2 + s2 + b1 / 2 ^ 26 := by omega
  have q3 : b3 = h3 + s3 + b2 / 2 ^ 26 := by omega
  have q4 : b4 = h4 + s4 + b3 / 2 ^ 26 := by omega
  subst q1 q2 q3 q4
  simp only [val5]
  omega

end VG.Proof.Poly1305.AArch64
