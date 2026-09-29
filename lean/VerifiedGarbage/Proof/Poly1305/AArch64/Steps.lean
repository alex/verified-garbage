import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit

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
  exact Nat.mod_lt _ (by decide)

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
    simp only [val5]; grind
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
  have r4 := Nat.lt_trans (lim4_lt hR) (show 2 ^ 24 < 2 ^ 26 by decide)
  have e := product_identity a0 a1 a2 a3 a4 (lim R 0) (lim R 1) (lim R 2) (lim R 3) (lim R 4)
  rw [val5_lim] at e
  -- Every product is less than `2⁵⁷`.
  have p : ∀ a j, a < 2 ^ 28 → j < 2 ^ 26 → a * j < 2 ^ 57 ∧ a * (5 * j) < 2 ^ 57 := by
    intro a j ha hj
    have h1 := mul_lt' ha hj
    have h2 := mul_lt' ha (show 5 * j < 5 * 2 ^ 26 by omega)
    exact ⟨by omega, by omega⟩
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
  have r2 : d1' = d1 + c0 := by omega_using [h0, h1, q0, q2]
  have r5 : d2' = d2 + c1 := by omega_using [h0, h1, h2, q0, q3, q5, r2]
  have r8 : d3' = d3 + c2 := by omega_using [h0, h1, h2, h3, q0, q3, q6, q8, r2, r5]
  have r11 : d4' = d4 + c2' := by omega_using [h0, h1, h2, h3, h4, q0, q3, q6, q9, q11, r2, r5, r8]
  have c4b : c4 < 2 ^ 35 := by omega_using [h0, h1, h2, h3, h4, q0, q3, q6, q9, q12, r2, r5, r8, r11]
  have r14 : q = c4 * 4 := by omega_using [c4b, q14]
  have r15 : c5 = c4 + q := by omega_using [c4b, q15, r14]
  have r16 : f = e0 + c5 := by omega_using [c4b, q1, q16, r14, r15]
  have r19 : g1 = e1 + c6 := by omega_using [c4b, q1, q4, q17, q19, r14, r15, r16]
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
  have ht2 : t2 = h2 + h1 / 2 ^ 26 := by omega_using [b1, b2, e2]
  have ht3 : t3 = h3 + t2 / 2 ^ 26 := by omega_using [b1, b2, b3, e4, ht2]
  have ht4 : t4 = h4 + t3 / 2 ^ 26 := by omega_using [b1, b2, b3, b4, e6, ht2, ht3]
  have hn : n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 ≤ 2 ^ 26 := by
    omega_using [b1, b2, b3, b4, e1, e3, e5, ht2, ht3, ht4]
  have hu0 : u0 = h0 + 5 := by omega_using [b0, f0]
  have hu1 : u1 = n1 + u0 / 2 ^ 26 := by omega_using [b0, hn, f2, hu0]
  have hu2 : u2 = n2 + u1 / 2 ^ 26 := by omega_using [b0, hn, f4, hu0, hu1]
  have hu3 : u3 = n3 + u2 / 2 ^ 26 := by omega_using [b0, hn, f6, hu0, hu1, hu2]
  have hu4 : u4 = t4 + u3 / 2 ^ 26 := by omega_using [b0, hn, f8, hu0, hu1, hu2, hu3]
  have hV : val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 := by
    simp only [val5]; omega_using [e1, e3, e5, ht2, ht3, ht4]
  have hG : val5 g0 g1 g2 g3 g4 + 2 ^ 130 * b = val5 h0 n1 n2 n3 t4 + 5 := by
    simp only [val5]; omega_using [f1, f3, f5, f7, f9, f10, hu0, hu1, hu2, hu3, hu4]
  rw [← hV]
  have hg : g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26 := by
    omega_using [f1, f3, f5, f7, f9]
  rcases (by omega_using [b0, hn, f10, hu0, hu1, hu2, hu3, hu4] : b = 0 ∨ b = 1) with h | h
  · right
    subst h
    simp only [val5] at hG
    have lt : val5 h0 n1 n2 n3 t4 < P := by simp only [val5]; rw [hP]; omega_using [hG, hg]
    exact ⟨rfl, (Nat.mod_eq_of_lt lt).symm, b0, hn.1, hn.2.1, hn.2.2.1, by omega_using [hG, hg]⟩
  · left
    subst h
    simp only [val5] at hG
    have ge : P ≤ val5 h0 n1 n2 n3 t4 := by simp only [val5]; rw [hP]; omega_using [hG, hg]
    have lt : val5 h0 n1 n2 n3 t4 - P < P := by simp only [val5]; rw [hP]; omega_using [hG, hg, hn, b0]
    refine ⟨rfl, ?_, hg⟩
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt, hP]
    simp only [val5]
    omega_using [hG, ge]

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
  have r0 : a0 = h0 + s0 := by omega_using [hh0, hs0, e0]
  have r1 : a1 = h1 + s1 := by omega_using [hh1, hs1, e1]
  have r2 : a2 = h2 + s2 := by omega_using [hh2, hs2, e2]
  have r3 : a3 = h3 + s3 := by omega_using [hh3, hs3, e3]
  have r4 : a4 = h4 + s4 := by omega_using [hh4, hs4, e4]
  subst r0 r1 r2 r3 r4
  have q1 : b1 = h1 + s1 + (h0 + s0) / 2 ^ 26 := by omega_using [hh0, hs0, hh1, hs1, c1]
  have q2 : b2 = h2 + s2 + b1 / 2 ^ 26 := by omega_using [hh0, hs0, hh1, hs1, hh2, hs2, c2, q1]
  have q3 : b3 = h3 + s3 + b2 / 2 ^ 26 := by
    omega_using [hh0, hs0, hh1, hs1, hh2, hs2, hh3, hs3, c3, q1, q2]
  have q4 : b4 = h4 + s4 + b3 / 2 ^ 26 := by
    omega_using [hh0, hs0, hh1, hs1, hh2, hs2, hh3, hs3, hh4, hs4, c4, q1, q2, q3]
  subst q1 q2 q3 q4
  simp only [val5]
  omega

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
  simp [exec, Size.bits, h]

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
  simp [hr]

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
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

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
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp)⟩
    have hw : (L.map fun q => v s₁ q.1 * word s₁ q.2) = (L.map fun q => v s q.1 * word s q.2) := by
      refine List.map_congr_left fun q hq => ?_
      obtain ⟨g1, g2, -, -⟩ := hL q (List.mem_cons_of_mem _ hq)
      simp only [v, word, x0₁, k₁.2.1, k₁.1 q.1 (not_mem2 g1 g2)]
    rw [e₂, hw, e₁, List.map_cons, List.sum_cons]
    omega


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
  refine WP.mono (macs_ok _ s₁ f1 f2 hL) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by simp)⟩
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
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2]

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
  simp [hr.1, hr.2]

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
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

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
    simp [hr.1, hr.2]

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
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]

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
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

theorem select_zero (h g : BitVec 64) : g ^^^ ((h ^^^ g) &&& 0) = g := by simp
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
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

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
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

end VG.Proof.Poly1305.AArch64
