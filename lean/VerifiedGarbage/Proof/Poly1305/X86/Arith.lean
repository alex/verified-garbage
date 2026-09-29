import Mathlib.Tactic.Ring
import VerifiedGarbage.Spec.Poly1305

/-!
# Poly1305 on x86 (32-bit): the arithmetic in radix `2³²`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/X86.lean`), as natural numbers: five words `a0, …, a4`
stand for `val5 a0 a1 a2 a3 a4 = a0 + 2³² a1 + 2⁶⁴ a2 + 2⁹⁶ a3 + 2¹²⁸ a4`,
and the clamped `r` for `r0 + 2³² 4 q1 + 2⁶⁴ 4 q2 + 2⁹⁶ 4 q3`, with
`sj = 5 qj`. The products are named so that `omega` treats them as atoms.
-/

namespace VG.Proof.Poly1305.X86

open VG.Spec.Poly1305 (P)

/-- The number with the words `a0, …, a4`. -/
def val5 (a0 a1 a2 a3 a4 : Nat) : Nat := a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4

/-- The clamped `r`, from `r0` and `rj = 4 qj`. -/
def rval (r0 q1 q2 q3 : Nat) : Nat := r0 + 2 ^ 32 * (4 * q1) + 2 ^ 64 * (4 * q2) + 2 ^ 96 * (4 * q3)

/-- `(a0 + … + 2¹²⁸ a4) r`: the terms of weight `2¹²⁸` and up but `a4 r0` are
folded into the bottom as multiples of `5 qj`, leaving a multiple of `p`. -/
theorem fold_identity (a0 a1 a2 a3 a4 r0 q1 q2 q3 : Nat) :
    val5 a0 a1 a2 a3 a4 * rval r0 q1 q2 q3 =
      (a0 * r0 + 5 * (a1 * q3) + 5 * (a2 * q2) + 5 * (a3 * q1)) +
      2 ^ 32 * (4 * (a0 * q1) + a1 * r0 + 5 * (a2 * q3) + 5 * (a3 * q2) + 5 * (a4 * q1)) +
      2 ^ 64 * (4 * (a0 * q2) + 4 * (a1 * q1) + a2 * r0 + 5 * (a3 * q3) + 5 * (a4 * q2)) +
      2 ^ 96 * (4 * (a0 * q3) + 4 * (a1 * q2) + 4 * (a2 * q1) + a3 * r0 + 5 * (a4 * q3)) +
      2 ^ 128 * (a4 * r0) +
      P * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) := by
  have hP : P + 5 = 2 ^ 130 := by simp [P]
  have e : val5 a0 a1 a2 a3 a4 * rval r0 q1 q2 q3 +
      5 * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) =
      (a0 * r0 + 5 * (a1 * q3) + 5 * (a2 * q2) + 5 * (a3 * q1)) +
      2 ^ 32 * (4 * (a0 * q1) + a1 * r0 + 5 * (a2 * q3) + 5 * (a3 * q2) + 5 * (a4 * q1)) +
      2 ^ 64 * (4 * (a0 * q2) + 4 * (a1 * q1) + a2 * r0 + 5 * (a3 * q3) + 5 * (a4 * q2)) +
      2 ^ 96 * (4 * (a0 * q3) + 4 * (a1 * q2) + 4 * (a2 * q1) + a3 * r0 + 5 * (a4 * q3)) +
      2 ^ 128 * (a4 * r0) +
      2 ^ 130 * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) := by
    simp only [val5, rval]; ring
  rw [← hP, Nat.add_mul] at e
  omega

theorem mul_le' {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := Nat.mul_le_mul h₁ h₂

/-- Absorbing a block (`products` and `carry`): from the words `a` of `h + m`
(`a4 ≤ 6`), the sums of products `dk` (each with the carry out of `d(k-1)`)
fit in 64 bits, `d4` in 32, and the result `w = t0 + 2³² t1 + 2⁶⁴ t2 + 2⁹⁶
t3 + 2¹²⁸ (d4 mod 4) + 5 ⌊d4 / 4⌋`, where `tk = dk mod 2³²`, is congruent to
`(h + m) r` modulo `p`, and less than `5 · 2¹²⁸`. -/
theorem absorb_arith {a0 a1 a2 a3 a4 r0 q1 q2 q3 d0 d1 d2 d3 d4 : Nat}
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32) (ha4 : a4 ≤ 6)
    (hr0 : r0 < 2 ^ 28) (hq1 : q1 < 2 ^ 26) (hq2 : q2 < 2 ^ 26) (hq3 : q3 < 2 ^ 26)
    (e0 : d0 = 0 + (a0 * r0 + (a1 * (5 * q3) + (a2 * (5 * q2) + (a3 * (5 * q1) + 0)))))
    (e1 : d1 = d0 / 2 ^ 32 + (a0 * (4 * q1) + (a1 * r0 + (a2 * (5 * q3) + (a3 * (5 * q2) +
      (a4 * (5 * q1) + 0))))))
    (e2 : d2 = d1 / 2 ^ 32 + (a0 * (4 * q2) + (a1 * (4 * q1) + (a2 * r0 + (a3 * (5 * q3) +
      (a4 * (5 * q2) + 0))))))
    (e3 : d3 = d2 / 2 ^ 32 + (a0 * (4 * q3) + (a1 * (4 * q2) + (a2 * (4 * q1) + (a3 * r0 +
      (a4 * (5 * q3) + 0))))))
    (e4 : d4 = d3 / 2 ^ 32 + a4 * r0) :
    d0 < 2 ^ 64 ∧ d1 < 2 ^ 64 ∧ d2 < 2 ^ 64 ∧ d3 < 2 ^ 64 ∧ d4 < 2 ^ 32 ∧ 5 * (d4 / 4) < 2 ^ 32 ∧
      (d0 % 2 ^ 32 + 2 ^ 32 * (d1 % 2 ^ 32) + 2 ^ 64 * (d2 % 2 ^ 32) + 2 ^ 96 * (d3 % 2 ^ 32) +
        2 ^ 128 * (d4 % 4) + 5 * (d4 / 4)) % P =
        (val5 a0 a1 a2 a3 a4 * rval r0 q1 q2 q3) % P := by
  have e := fold_identity a0 a1 a2 a3 a4 r0 q1 q2 q3
  -- Every product, bounded.
  have b : ∀ a q, a < 2 ^ 32 → q < 2 ^ 26 → a * q ≤ (2 ^ 32 - 1) * (2 ^ 26 - 1) :=
    fun a q h h' => mul_le' (by omega) (by omega)
  have br : ∀ a, a < 2 ^ 32 → a * r0 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1) :=
    fun a h => mul_le' (by omega) (by omega)
  have p01 := b a0 q1 ha0 hq1; have p02 := b a0 q2 ha0 hq2; have p03 := b a0 q3 ha0 hq3
  have p11 := b a1 q1 ha1 hq1; have p12 := b a1 q2 ha1 hq2; have p13 := b a1 q3 ha1 hq3
  have p21 := b a2 q1 ha2 hq1; have p22 := b a2 q2 ha2 hq2; have p23 := b a2 q3 ha2 hq3
  have p31 := b a3 q1 ha3 hq1; have p32 := b a3 q2 ha3 hq2; have p33 := b a3 q3 ha3 hq3
  have p41 : a4 * q1 ≤ 6 * (2 ^ 26 - 1) := mul_le' ha4 (by omega)
  have p42 : a4 * q2 ≤ 6 * (2 ^ 26 - 1) := mul_le' ha4 (by omega)
  have p43 : a4 * q3 ≤ 6 * (2 ^ 26 - 1) := mul_le' ha4 (by omega)
  have p00 := br a0 ha0; have p10 := br a1 ha1; have p20 := br a2 ha2; have p30 := br a3 ha3
  have p40 : a4 * r0 ≤ 6 * (2 ^ 28 - 1) := mul_le' ha4 (by omega)
  -- Named products for `omega`.
  have m4 : ∀ a q, a * (4 * q) = 4 * (a * q) := fun a q => by ring
  have m5 : ∀ a q, a * (5 * q) = 5 * (a * q) := fun a q => by ring
  rw [m5, m5, m5] at e0
  rw [m4, m5, m5, m5] at e1
  rw [m4, m4, m5, m5] at e2
  rw [m4, m4, m4, m5] at e3
  generalize a0 * r0 = x00 at *; generalize a1 * r0 = x10 at *; generalize a2 * r0 = x20 at *
  generalize a3 * r0 = x30 at *; generalize a4 * r0 = x40 at *
  generalize a0 * q1 = x01 at *; generalize a0 * q2 = x02 at *; generalize a0 * q3 = x03 at *
  generalize a1 * q1 = x11 at *; generalize a1 * q2 = x12 at *; generalize a1 * q3 = x13 at *
  generalize a2 * q1 = x21 at *; generalize a2 * q2 = x22 at *; generalize a2 * q3 = x23 at *
  generalize a3 * q1 = x31 at *; generalize a3 * q2 = x32 at *; generalize a3 * q3 = x33 at *
  generalize a4 * q1 = x41 at *; generalize a4 * q2 = x42 at *; generalize a4 * q3 = x43 at *
  generalize val5 a0 a1 a2 a3 a4 * rval r0 q1 q2 q3 = AR at *
  have hP : P = 2 ^ 130 - 5 := rfl
  have b0 : d0 < 2 ^ 63 := by omega
  have b1 : d1 < 2 ^ 63 := by omega
  have b2 : d2 < 2 ^ 63 := by omega
  have b3 : d3 < 2 ^ 62 + 2 ^ 32 := by omega
  have b4 : d4 < 2 ^ 31 + 2 ^ 30 := by omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [e, show (x00 + 5 * x13 + 5 * x22 + 5 * x31) +
      2 ^ 32 * (4 * x01 + x10 + 5 * x23 + 5 * x32 + 5 * x41) +
      2 ^ 64 * (4 * x02 + 4 * x11 + x20 + 5 * x33 + 5 * x42) +
      2 ^ 96 * (4 * x03 + 4 * x12 + 4 * x21 + x30 + 5 * x43) + 2 ^ 128 * x40 =
      d0 % 2 ^ 32 + 2 ^ 32 * (d1 % 2 ^ 32) + 2 ^ 64 * (d2 % 2 ^ 32) + 2 ^ 96 * (d3 % 2 ^ 32) +
      2 ^ 128 * (d4 % 4) + 5 * (d4 / 4) + P * (d4 / 4) by rw [hP]; omega,
    Nat.add_assoc _ (P * _), ← Nat.mul_add, Nat.add_mul_mod_self_left]

/-- The words of `h` after a block is absorbed (`carry`): `w` (see
`absorb_arith`) in five words, with carries; the top one is at most 4. -/
theorem carry_arith {t0 t1 t2 t3 d4 e u0 u1 u2 u3 u4 : Nat} (ht0 : t0 < 2 ^ 32)
    (ht1 : t1 < 2 ^ 32) (ht2 : t2 < 2 ^ 32) (ht3 : t3 < 2 ^ 32)
    (he : e < 2 ^ 32) (hu0 : u0 = (e + t0) % 2 ^ 32)
    (hu1 : u1 = (t1 + (e + t0) / 2 ^ 32) % 2 ^ 32)
    (hu2 : u2 = (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu3 : u3 = (t3 + (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu4 : u4 = (d4 % 4 + (t3 + (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    val5 u0 u1 u2 u3 u4 = t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 + 2 ^ 128 * (d4 % 4) + e ∧
      u4 ≤ 4 := by
  simp only [val5]
  omega

/-- Adding a block `m0 + … + 2⁹⁶ m3 + 2¹²⁸ pad` to `h` with `h4 ≤ 4` (`addBlock`):
the words of the sum, the top one at most 6. -/
theorem add_arith {h0 h1 h2 h3 h4 m0 m1 m2 m3 pad u0 u1 u2 u3 u4 : Nat} (hh0 : h0 < 2 ^ 32)
    (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32) (hh4 : h4 ≤ 4) (hm0 : m0 < 2 ^ 32)
    (hm1 : m1 < 2 ^ 32) (hm2 : m2 < 2 ^ 32) (hm3 : m3 < 2 ^ 32) (hpad : pad ≤ 1)
    (hu0 : u0 = (h0 + m0) % 2 ^ 32)
    (hu1 : u1 = (h1 + m1 + (h0 + m0) / 2 ^ 32) % 2 ^ 32)
    (hu2 : u2 = (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu3 : u3 = (h3 + m3 + (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu4 : u4 = (h4 + pad + (h3 + m3 + (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) /
      2 ^ 32) % 2 ^ 32) :
    val5 u0 u1 u2 u3 u4 = val5 h0 h1 h2 h3 h4 + (m0 + 2 ^ 32 * m1 + 2 ^ 64 * m2 + 2 ^ 96 * m3 +
      2 ^ 128 * pad) ∧ u4 ≤ 6 := by
  simp only [val5]
  omega

/-- The final reduction (`plus5`, `selectWord`, `selectTop`): `g = h + 5` in
words (`g4` the top one, not reduced), and `b = ⌊g4 / 4⌋`. If `b = 1`, `g -
2¹³⁰` (the words `g0, …, g3, g4 mod 4`) is `h mod p`, and otherwise `h` (whose
top word is `h4 mod 4`) is. -/
theorem reduce_arith {h0 h1 h2 h3 h4 g0 g1 g2 g3 g4 : Nat} (hh0 : h0 < 2 ^ 32)
    (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32) (hh4 : h4 ≤ 4)
    (e0 : g0 = (h0 + 5) % 2 ^ 32) (e1 : g1 = (h1 + (h0 + 5) / 2 ^ 32) % 2 ^ 32)
    (e2 : g2 = (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (e3 : g3 = (h3 + (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (e4 : g4 = (h4 + (h3 + (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    (g4 / 4 = 1 ∧ val5 g0 g1 g2 g3 (g4 % 4) = val5 h0 h1 h2 h3 h4 % P) ∨
      (g4 / 4 = 0 ∧ val5 h0 h1 h2 h3 (h4 % 4) = val5 h0 h1 h2 h3 h4 % P) := by
  have hP : P = 2 ^ 130 - 5 := rfl
  have hg : val5 g0 g1 g2 g3 g4 = val5 h0 h1 h2 h3 h4 + 5 := by simp only [val5]; omega
  have hg4 : g4 ≤ 5 := by omega
  rcases (by omega : g4 / 4 = 1 ∨ g4 / 4 = 0) with hb | hb
  · left
    refine ⟨hb, ?_⟩
    have ge : P ≤ val5 h0 h1 h2 h3 h4 := by simp only [val5] at hg ⊢; omega
    have lt : val5 h0 h1 h2 h3 h4 - P < P := by simp only [val5] at hg ⊢; omega
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    simp only [val5] at hg ⊢
    omega
  · right
    refine ⟨hb, ?_⟩
    have lt : val5 h0 h1 h2 h3 h4 < P := by simp only [val5] at hg ⊢; omega
    rw [Nat.mod_eq_of_lt lt]
    simp only [val5] at hg ⊢
    omega

/-- The tag's words (`addS`): `x + s` modulo `2¹²⁸`, in four words, with carries. -/
theorem addS_arith {x0 x1 x2 x3 s0 s1 s2 s3 : Nat} (X S : Nat)
    (hX : X % 2 ^ 128 = x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3)
    (hS : S = s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3) :
    (x0 + s0) % 2 ^ 32 = (X + S) % 2 ^ 32 ∧
    (x1 + s1 + (x0 + s0) / 2 ^ 32) % 2 ^ 32 = (X + S) / 2 ^ 32 % 2 ^ 32 ∧
    (x2 + s2 + (x1 + s1 + (x0 + s0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32 = (X + S) / 2 ^ 64 % 2 ^ 32 ∧
    (x3 + s3 + (x2 + s2 + (x1 + s1 + (x0 + s0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32 =
      (X + S) / 2 ^ 96 % 2 ^ 32 := by
  subst hS
  refine ⟨by omega, by omega, by omega, by omega⟩

end VG.Proof.Poly1305.X86
