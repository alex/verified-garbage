import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Lit

section

/-!
# Poly1305 on x86 (32-bit): the arithmetic in radix `2³²`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/X86.lean`), as natural numbers: five words `a0, …, a4`
stand for `val5 a0 a1 a2 a3 a4 = a0 + 2³² a1 + 2⁶⁴ a2 + 2⁹⁶ a3 + 2¹²⁸ a4`,
and the clamped `r` for `r0 + 2³² 4 q1 + 2⁶⁴ 4 q2 + 2⁹⁶ 4 q3`, with
`sj = 5 qj`. The products are named so that `omega` treats them as atoms.
-/

open VG.PowLit

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
    simp only [val5, rval]; grind
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
  have m4 : ∀ a q, a * (4 * q) = 4 * (a * q) := fun a q => Nat.mul_left_comm _ _ _
  have m5 : ∀ a q, a * (5 * q) = 5 * (a * q) := fun a q => Nat.mul_left_comm _ _ _
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
  have b0 : d0 < 2 ^ 63 := by omega_using [e0, p00, p13, p22, p31]
  have b1 : d1 < 2 ^ 63 := by omega_using [b0, e1, p01, p10, p23, p32, p41]
  have b2 : d2 < 2 ^ 63 := by omega_using [b1, e2, p02, p11, p20, p33, p42]
  have b3 : d3 < 2 ^ 62 + 2 ^ 32 := by omega_using [b2, e3, p03, p12, p21, p30, p43]
  have b4 : d4 < 2 ^ 31 + 2 ^ 30 := by omega_using [b3, e4, p40]
  refine ⟨by omega_using [b0], by omega_using [b1], by omega_using [b2], by omega_using [b3],
    by omega_using [b4], by omega_using [b4], ?_⟩
  rw [e, show (x00 + 5 * x13 + 5 * x22 + 5 * x31) +
      2 ^ 32 * (4 * x01 + x10 + 5 * x23 + 5 * x32 + 5 * x41) +
      2 ^ 64 * (4 * x02 + 4 * x11 + x20 + 5 * x33 + 5 * x42) +
      2 ^ 96 * (4 * x03 + 4 * x12 + 4 * x21 + x30 + 5 * x43) + 2 ^ 128 * x40 =
      d0 % 2 ^ 32 + 2 ^ 32 * (d1 % 2 ^ 32) + 2 ^ 64 * (d2 % 2 ^ 32) + 2 ^ 96 * (d3 % 2 ^ 32) +
      2 ^ 128 * (d4 % 4) + 5 * (d4 / 4) + P * (d4 / 4) by rw [hP]; omega_using [e0, e1, e2, e3, e4],
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
  have hb : g0 < 2 ^ 32 ∧ g1 < 2 ^ 32 ∧ g2 < 2 ^ 32 ∧ g3 < 2 ^ 32 ∧ g4 ≤ 5 := by
    omega_using [hh0, hh1, hh2, hh3, hh4, e0, e1, e2, e3, e4]
  simp only [val5] at hg ⊢
  rcases (by omega_using [hb] : g4 / 4 = 1 ∨ g4 / 4 = 0) with h | h
  · left
    refine ⟨h, ?_⟩
    have ge : P ≤ h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4 := by
      omega_using [hg, hb, h, hP]
    have lt : h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4 - P < P := by
      omega_using [hg, hb, h, hP]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [hg, hb, h, hP]
  · right
    refine ⟨h, ?_⟩
    have lt : h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 + 2 ^ 128 * h4 < P := by
      omega_using [hg, hb, h, hP]
    rw [Nat.mod_eq_of_lt lt]
    omega_using [hg, hb, h, hh0, hh1, hh2, hh3, hh4]

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

end

/-!
# Poly1305 on x86 (32-bit): the steps of the code

Untrusted: everything here is checked by Lean. Each lemma runs a few
instructions symbolically and states their effect on the numbers in the
registers and the words in memory.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- Two states agree except on the registers `rs` (and the flags), in memory
and regions. -/
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

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 32-bit word at `[x + d]`. -/
abbrev wd (m : Mem) (x : BitVec 32) (d : Nat) : BitVec 32 := m.readW (addr x d) 32

/-- The same, as a number. -/
abbrev wv (m : Mem) (x : BitVec 32) (d : Nat) : Nat := (wd m x d).toNat

/-! ## Addresses and regions -/

theorem addr_toNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (addr x d).toNat = x.toNat + d := by
  rw [addr_eq h, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := d) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The region of `n` bytes at `[x + d]`. -/
abbrev sub (x : BitVec 32) (d n : Nat) : Region := ⟨addr x d, n⟩

theorem sub_contains {x : BitVec 32} {a k d n : Nat} (hx : x.toNat + a + k ≤ 2 ^ 32) (h₁ : a ≤ d)
    (h₂ : d + n ≤ a + k) (hn : 0 < n) : (sub x a k).Contains (addr x d) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have := x.isLt
  have hb : (x.setWidth 64).toNat < 2 ^ 32 := by rw [BitVec.toNat_setWidth]; omega
  generalize x.setWidth 64 = b at *
  have : (b + BitVec.ofNat 64 d - (b + BitVec.ofNat 64 a)).toNat = d - a := by bv_omega
  omega

theorem sub_disj {x : BitVec 32} {d n e k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32)
    (he : x.toNat + e + k ≤ 2 ^ 32) (h : d + n ≤ e ∨ e + k ≤ d) : (sub x d n).Disjoint (sub x e k) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  by_cases hn : n = 0
  · omega
  by_cases hk : k = 0
  · omega
  rw [addr_eq (by omega)] at h₁
  rw [addr_eq (by omega)] at h₂
  have hb : (x.setWidth 64).toNat < 2 ^ 32 := by rw [BitVec.toNat_setWidth]; have := x.isLt; omega
  generalize x.setWidth 64 = b at *
  bv_omega

/-- The 32-bit word at `[x + d]`, after a store at `[x + e]` that does not overlap it. -/
theorem wd_write_ne (m : Mem) {x : BitVec 32} (w : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    wd (m.writeW (addr x e) w) x d = wd m x d :=
  Mem.readW_writeW_sep ((sub_disj hd he h).sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by decide)

theorem wd_write_self (m : Mem) (x : BitVec 32) (w : BitVec 32) (d : Nat) :
    wd (m.writeW (addr x d) w) x d = w :=
  Mem.readW_writeW_self32 _ _ _

/-- A word outside the regions a frame allows to change. -/
theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : BitVec 32} {d : Nat}
    (hd : ∀ r ∈ rs, (sub x d 4).Disjoint r) : wd m' x d = wd m x d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The state's region. -/
abbrev sR (st : BitVec 32) : Region := ⟨st.setWidth 64, 128⟩

theorem sR_contains {st : BitVec 32} (hst : st.toNat + 128 ≤ 2 ^ 32) {d n : Nat} (h : d + n ≤ 128)
    (hn : 0 < n) : (sR st).Contains (addr st d) n := by
  have := sub_contains (x := st) (a := 0) (k := 128) (by omega) (Nat.zero_le d) (by omega) hn
  simpa [sub, addr] using this

/-- The code's view of the state: `edi` points at it, it is writable, and it
does not wrap around the 32-bit address space. -/
structure Ctx (st : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = st
  fit : st.toNat + 128 ≤ 2 ^ 32
  wr : sR st ∈ s.wr

namespace Ctx
variable {st : BitVec 32} {s : State} (h : Ctx st s)
include h

theorem inW {d n : Nat} (hd : d + n ≤ 128) (hn : 0 < n) : InRegions s.wr (addr st d) n :=
  ⟨_, h.wr, sR_contains h.fit hd hn⟩

theorem inRW {d n : Nat} (hd : d + n ≤ 128) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (addr st d) n :=
  ⟨_, List.mem_append_right _ h.wr, sR_contains h.fit hd hn⟩

theorem inW' {d : Nat} (hd : d + 4 ≤ 128) : InRegions s.wr (addr (s.gpr .edi) d) 4 := by
  rw [h.edi]; exact h.inW hd (by omega)

theorem inRW' {d : Nat} (hd : d + 4 ≤ 128) : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) d) 4 := by
  rw [h.edi]; exact h.inRW hd (by omega)

/-- The context survives a change of other registers and of memory. -/
theorem keep {s' : State} (he : s'.gpr .edi = s.gpr .edi) (hw : s'.wr = s.wr) : Ctx st s' :=
  ⟨he.trans h.edi, h.fit, hw ▸ h.wr⟩

theorem wd_ne (m : Mem) (w : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 128) (he : e + 4 ≤ 128)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : wd (m.writeW (addr st e) w) st d = wd m st d :=
  wd_write_ne m w (by have := h.fit; omega) (by have := h.fit; omega) hde

end Ctx

/-- The accumulator of a sum of products, `ebx + 2³² ebp`. -/
abbrev acc (s : State) : Nat := v s .ebx + 2 ^ 32 * v s .ebp

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem carry_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by
  cases c <;> rfl

theorem toNat_mul_lo (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat * b.toNat)).toNat +
      2 ^ 32 * (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = a.toNat * b.toNat := by
  have := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 32) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega)]
  omega

/-- An addition with carry into a second word, as numbers, when the sum fits. -/
theorem add_adc_toNat (a b c d : BitVec 32)
    (h : a.toNat + b.toNat + 2 ^ 32 * (c.toNat + d.toNat) < 2 ^ 64) :
    (a + b).toNat + 2 ^ 32 * (c + d + (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + b.toNat))).setWidth 32).toNat =
      a.toNat + b.toNat + 2 ^ 32 * (c.toNat + d.toNat) := by
  simp only [BitVec.toNat_add, carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h2, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `ebx:ebp += hi · c`, the coefficient `c` at `[edi + off]`. -/
theorem mac_ok (s : State) (i off : Nat)
    (h1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff i)) 4)
    (h2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) off) 4) :
    WP isa (.block (mac i off)) s fun s' =>
      (acc s + wv s.mem (s.gpr .edi) (hOff i) * wv s.mem (s.gpr .edi) off < 2 ^ 64 →
        acc s' = acc s + wv s.mem (s.gpr .edi) (hOff i) * wv s.mem (s.gpr .edi) off) ∧
      Keeps [.eax, .ecx, .edx, .ebx, .ebp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mac, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, ea_at, acc, v, wv, wd, State.load32, execMul, execAlu, arithFlags, State.setReg, State.setFlags, h1, h2,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := toNat_mul_lo (s.mem.readW (addr (s.gpr .edi) (hOff i)) 32)
      (s.mem.readW (addr (s.gpr .edi) off) 32)
    rw [add_adc_toNat _ _ _ _ (by have := (s.gpr .ebp).isLt; omega)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

/-- A chain of `mac`s. -/
theorem macs_ok (L : List (Nat × Nat)) (s : State)
    (hL : ∀ p ∈ L, InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff p.1)) 4 ∧
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) p.2) 4) :
    WP isa (.block (L.flatMap fun p => mac p.1 p.2)) s fun s' =>
      (acc s + (L.map fun p => wv s.mem (s.gpr .edi) (hOff p.1) * wv s.mem (s.gpr .edi) p.2).sum <
          2 ^ 64 →
        acc s' = acc s + (L.map fun p => wv s.mem (s.gpr .edi) (hOff p.1) * wv s.mem (s.gpr .edi) p.2).sum) ∧
      Keeps [.eax, .ecx, .edx, .ebx, .ebp] s s' := by
  induction L generalizing s with
  | nil => exact WP.block_nil ⟨fun _ => by simp, Keeps.refl _ _⟩
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := hL p List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (mac_ok s p.1 p.2 h1 h2) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have edi₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr'
    have hL' : ∀ q ∈ L, InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edi) (hOff q.1)) 4 ∧
        InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edi) q.2) 4 := fun q hq => by
      rw [k₁.2.2.1, k₁.2.2.2, edi₁]; exact hL q (List.mem_cons_of_mem _ hq)
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨fun hlt => ?_, (k₁.trans k₂).mono (by simp)⟩
    rw [edi₁, k₁.2.1] at e₂
    simp only [List.map_cons, List.sum_cons] at hlt ⊢
    rw [e₂ (by rw [e₁ (by omega)]; omega), e₁ (by omega)]
    omega


/-! ## One instruction at a time

Continuation-style rules that expose only what an instruction changes. -/

/-- `s'` is `s` with register `d` set to `w` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (w : BitVec 32) : Prop where
  gpr : s'.gpr d = w
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (w : BitVec 32) : Upd s (s.setReg d w) d w :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (w : BitVec 32) :
    Upd s ((arithFlags s x c o).setReg d w) d w :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, arithFlags, State.setFlags, h], rfl, rfl, rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (w : BitVec 32) :
    Upd s ((s.setFlags c o z n).setReg d w) d w :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cf : s'.cf = s.cf
  zf : s'.zf = s.zf

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_movi {d : Reg} {w : BitVec 32}
    (k : ∀ s', Upd s s' d w → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm w) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.mem.readW a 32) → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 32)) ?_ (k _ (Upd.setReg _ _ _) rfl)
  simp [exec, readSrc, State.load32, ha, hin]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ha, hout]

/-- `add d, src` for a source of value `x`: the sum, and its carry out. -/
theorem wp_addx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', Upd s s' d (s.gpr d + x) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d + x) (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat))
    (addOverflow (s.gpr d) x (s.gpr d + x)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `adc d, src` for a source of value `x`, with the carry `c` in: the sum,
and its carry out. -/
theorem wp_adcx {d : Reg} {src : Src} {x : BitVec 32} {c : Bool} (hx : readSrc s src = some x)
    (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + x + (BitVec.ofBool c).setWidth 32) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat + c.toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d + x + (BitVec.ofBool c).setWidth 32)
    (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat + c.toNat))
    (addOverflow (s.gpr d) x (s.gpr d + x + (BitVec.ofBool c).setWidth 32)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some, hc, Option.map_some]

theorem wp_andx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', Upd s s' d (s.gpr d &&& x) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d &&& x) false false _))
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_xorx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ x) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d ^^^ x) false false _))
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_subx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', Upd s s' d (s.gpr d - x) → s'.zf = some (s.gpr d - x == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d - x) (decide ((s.gpr d).toNat < x.toNat))
    (subOverflow (s.gpr d) x (s.gpr d - x)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `cmp d, src` for a source of value `x`: ZF and CF of `d - x`. -/
theorem wp_cmpx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', Keeps [] s s' → s'.zf = some (s.gpr d - x == 0) →
      s'.cf = some (decide ((s.gpr d).toNat < x.toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q := by
  refine WP.cons ?_ (k (arithFlags s (s.gpr d - x) (decide ((s.gpr d).toNat < x.toNat))
    (subOverflow (s.gpr d) x (s.gpr d - x))) ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_test {d : Reg}
    (k : ∀ s', Keeps [] s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ha, hout]

end

theorem readSrc_imm (s : State) (w : BitVec 32) : readSrc s (.imm w) = some w := rfl
theorem readSrc_reg (s : State) (r : Reg) : readSrc s (.reg r) = some (s.gpr r) := rfl

theorem readSrc_mem {s : State} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) : readSrc s (.mem m) = some (s.mem.readW a 32) := by
  simp [readSrc, State.load32, ha, hin]

theorem add3_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, carry_toNat, Nat.mod_add_mod]


/-! ## The state as words

The state's 32 words, as numbers, are a function `f`; a store of a word
updates it (`upd`). -/

/-- The state's words at `st` are `f`. -/
def Words (m : Mem) (st : BitVec 32) (f : Nat → Nat) : Prop := ∀ k < 32, wv m st (4 * k) = f k

/-- `f` with word `j` replaced by `x`. -/
def upd (f : Nat → Nat) (j x : Nat) : Nat → Nat := fun k => if k = j then x else f k

theorem upd_same (f : Nat → Nat) (j x : Nat) : upd f j x j = x := by simp [upd]

theorem upd_ne (f : Nat → Nat) {j k : Nat} (x : Nat) (h : k ≠ j) : upd f j x k = f k := by simp [upd, h]

theorem Words.write {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : Words m st f)
    (hfit : st.toNat + 128 ≤ 2 ^ 32) {j : Nat} (hj : j < 32) (w : BitVec 32) :
    Words (m.writeW (addr st (4 * j)) w) st (upd f j w.toNat) := by
  intro k hk
  by_cases e : k = j
  · subst e; rw [upd_same, wv, wd_write_self]
  · rw [upd_ne _ _ e, wv, wd_write_ne m w (by omega) (by omega) (by omega)]; exact h k hk

theorem Words.readW {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : Words m st f) {k : Nat}
    (hk : k < 32) : (m.readW (addr st (4 * k)) 32).toNat = f k := h k hk

theorem Words.lt {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : Words m st f) {k : Nat}
    (hk : k < 32) : f k < 2 ^ 32 := by
  rw [← h k hk]; exact BitVec.isLt _

/-- Stores to the state stay in its region. -/
theorem frame_write {m m' : Mem} {st : BitVec 32} (hf : Frame [sR st] m m')
    (hfit : st.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 128) (w : BitVec 32) :
    Frame [sR st] m (m'.writeW (addr st d) w) :=
  hf.writeW (List.mem_singleton_self _) _ (sR_contains hfit hd (by omega))

/-- What code leaves that writes only the state: its words `g`, the rest of
memory, the registers but `rs`, and the regions. -/
structure After (st : BitVec 32) (s s' : State) (g : Nat → Nat) (rs : List Reg) : Prop where
  words : Words s'.mem st g
  frame : Frame [sR st] s.mem s'.mem
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

namespace After
variable {st : BitVec 32} {s s₁ s₂ : State} {g g₁ g₂ : Nat → Nat} {rs rs₁ rs₂ : List Reg}

theorem ctx (h : After st s s₁ g rs) (hc : Ctx st s) (he : Reg.edi ∉ rs := by decide) : Ctx st s₁ :=
  hc.keep (h.gpr _ he) h.wr

theorem trans (h₁ : After st s s₁ g₁ rs₁) (h₂ : After st s₁ s₂ g₂ rs₂) : After st s s₂ g₂ (rs₁ ++ rs₂) :=
  ⟨h₂.words, h₁.frame.trans h₂.frame, fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem mono {rs' : List Reg} (h : After st s s₁ g rs) (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : After st s s₁ g rs' :=
  ⟨h.words, h.frame, fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

/-- A word of a region disjoint from the state, unchanged. -/
theorem wd (h : After st s s₁ g rs) {x : BitVec 32} {d : Nat} (hd : (sub x d 4).Disjoint (sR st)) :
    X86.wd s₁.mem x d = X86.wd s.mem x d :=
  wd_frame h.frame (by simpa using hd)

end After

/-- `mov eax, [edi + 4 j]; op eax, src; mov [edi + 4 j'], eax` with `op` an
addition of the source's value `x` and the carry `cin`: the sum is stored, and
CF is its carry out. -/
theorem los_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat} (hw : Words s.mem st f)
    {a b j j' : Nat} (ha : a = 4 * j) (hb : b = 4 * j') (hj : j < 32) (hj' : j' < 32)
    {op : AluOp} {src : Src} {cin : Bool} {x : BitVec 32}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin))
    (hsrc : ∀ s' y, Upd s s' .eax y → readSrc s' src = some x) :
    WP isa (.block [.mov .eax (.mem (at_ .edi a)), .alu op .eax src, .store (at_ .edi b) .eax]) s
      fun s' => After st s s' (upd f j' ((f j + x.toNat + cin.toNat) % 2 ^ 32)) [.eax] ∧
        s'.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) := by
  subst ha hb
  have hfit := hc.fit
  refine wp_movm (a := addr st (4 * j)) (by rw [ea_at, hc.edi]) (hc.inRW (by omega) (by omega))
    fun s₁ u₁ cf₁ => ?_
  have hx := hsrc s₁ _ u₁
  have e₁ : (s₁.gpr .eax).toNat = f j := by rw [u₁.gpr]; exact hw j hj
  -- The last step, for both operations.
  have fin : ∀ (s₂ : State) (y : BitVec 32), Upd s₁ s₂ .eax y → y.toNat = (f j + x.toNat + cin.toNat) % 2 ^ 32 →
      s₂.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) →
      WP isa (.block [.store (at_ .edi (4 * j')) .eax]) s₂ fun s' =>
        After st s s' (upd f j' ((f j + x.toNat + cin.toNat) % 2 ^ 32)) [.eax] ∧
        s'.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) := by
    intro s₂ y u₂ hy cf₂
    have edi₂ : s₂.gpr .edi = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
    refine wp_store (a := addr st (4 * j')) (by rw [ea_at, edi₂])
      (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega)) fun s₃ u₃ => WP.block_nil ?_
    rw [u₂.gpr] at u₃
    refine ⟨⟨?_, ?_, fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩,
      by rw [u₃.cf]; exact cf₂⟩
    · rw [u₃.mem, u₂.mem, u₁.mem, ← hy]; exact hw.write hfit hj' y
    · rw [u₃.mem, u₂.mem, u₁.mem]; exact frame_write (Frame.refl _ _) hfit (by omega) y
    · simp only [List.mem_singleton] at hr
      rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hcf⟩
  · refine wp_addx hx fun s₂ u₂ cf₂ => fin s₂ _ u₂ ?_ (by rw [cf₂, e₁]; rfl)
    rw [BitVec.toNat_add, e₁]; rfl
  · refine wp_adcx hx (by rw [cf₁]; exact hcf) fun s₂ u₂ cf₂ => fin s₂ _ u₂ ?_ (by rw [cf₂, e₁])
    rw [add3_toNat, e₁]


/-! ## Adding a block -/

/-- A word of the block at `b + d` as a source, in any state that differs only in `eax`. -/
theorem src_blk {s : State} {b : Reg} (hb : b ≠ .eax) {d : Nat} {a : Addr} (hea : addr (s.gpr b) d = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) :
    ∀ s' y, Upd s s' .eax y → readSrc s' (.mem (at_ b d)) = some (s.mem.readW a 32) := by
  intro s' y u
  rw [readSrc_mem (a := a) (by rw [ea_at, u.other _ hb, hea]) (by rw [u.rd, u.wr]; exact hin), u.mem]

theorem src_imm {s : State} (w : BitVec 32) :
    ∀ s' y, Upd s s' .eax y → readSrc s' (.imm w) = some w := fun _ _ _ => rfl

/-- Word `i` of the block at `b + d` (word `i` at `bp`) added to word `i` of
`h`, with the carry in unless `i = 0`. -/
theorem addWord_ok {st bp : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat}
    (hw : Words s.mem st f) {b : Reg} (hb : b ≠ .eax) {d i : Nat} (hi : i < 4)
    (hea : addr (s.gpr b) (d + 4 * i) = addr bp (4 * i)) {cin : Bool}
    (hop : (i = 0 ∧ cin = false) ∨ (i ≠ 0 ∧ s.cf = some cin))
    (hin : InRegions (s.rd ++ s.wr) (addr bp (4 * i)) 4) :
    WP isa (.block (addWord b d i)) s fun s' =>
      After st s s' (upd f i ((f i + wv s.mem bp (4 * i) + cin.toNat) % 2 ^ 32)) [.eax] ∧
      s'.cf = some (decide (2 ^ 32 ≤ f i + wv s.mem bp (4 * i) + cin.toNat)) :=
  los_ok hc hw rfl rfl (by omega) (by omega)
    (by rcases hop with ⟨rfl, rfl⟩ | ⟨h, h'⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨by simp [h], h'⟩)
    (src_blk hb hea hin)

end VG.Proof.Poly1305.X86
