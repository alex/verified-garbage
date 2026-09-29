import VerifiedGarbage.Spec.Poly1305
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.RingNF

/-!
# Poly1305 on x86-64: the arithmetic of a block

Untrusted: everything here is checked by Lean. The numbers the code computes
while absorbing a block (see `Impl/Poly1305/X86_64.lean`), as natural
numbers: the accumulator `h = h0 + 2⁶⁴ h1 + 2¹²⁸ h2`, the clamped
`r = r0 + 2⁶⁴ r1` with `r1 = 4 q`, and `s1 = 5 q`. The products are named
(`h0 * r0`, …) so that `omega` treats them as atoms.
-/

namespace VG.Proof.Poly1305.X86_64

open VG.Spec.Poly1305 (P)

theorem mul_lt {a b c d : Nat} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  Nat.mul_lt_mul_of_lt_of_lt h₁ h₂

theorem mul_le_lt {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c < d) : a * c ≤ b * d :=
  Nat.mul_le_mul h₁ h₂.le

/-- The bounds that make every sum of products fit its registers. -/
theorem absorb_bounds {h0 h1 h2 r0 q : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6)
    (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58) :
    h0 * r0 < 2 ^ 124 ∧ h1 * (5 * q) < 2 ^ 125 ∧ h0 * (4 * q) < 2 ^ 124 ∧ h1 * r0 < 2 ^ 124 ∧
      h2 * (5 * q) < 2 ^ 64 ∧ h2 * r0 ≤ 6 * r0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_lt hh0 hr0; norm_num at this ⊢; omega
  · have := mul_lt hh1 (show 5 * q < 5 * 2 ^ 58 by omega); norm_num at this ⊢; omega
  · have := mul_lt hh0 (show 4 * q < 4 * 2 ^ 58 by omega); norm_num at this ⊢; omega
  · have := mul_lt hh1 hr0; norm_num at this ⊢; omega
  · have := mul_le_lt hh2 (show 5 * q < 5 * 2 ^ 58 by omega); norm_num at this ⊢; omega
  · exact Nat.mul_le_mul_right _ hh2

/-- `(h0 + 2⁶⁴ h1 + 2¹²⁸ h2) (r0 + 2⁶⁴ 4 q)`, expanded into the named products. -/
theorem expand (h0 h1 h2 r0 q : Nat) :
    (h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q)) =
      h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) := by
  ring

/-- Absorbing a block: `x = x0 + 2⁶⁴ x1 = h0 r0 + h1 s1`, `y = y0 + 2⁶⁴ y1 =
h0 r1 + h1 r0 + h2 s1`, `u0 + 2⁶⁴ c1 = y0 + x1`, the top word `t = y1 + h2 r0 +
c1`, and the result `w = x0 + 5 ⌊t / 4⌋ + 2⁶⁴ u0 + 2¹²⁸ (t mod 4)` in three
words: `w ≡ h r` modulo `p`, and `w2 ≤ 4`. -/
theorem absorb_arith {h0 h1 h2 r0 q x0 x1 y0 y1 u0 c1 w0 w1 w2 : Nat}
    (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64) (hh2 : h2 ≤ 6) (hr0 : r0 < 2 ^ 60) (hq : q < 2 ^ 58)
    (hx : x0 + 2 ^ 64 * x1 = h0 * r0 + h1 * (5 * q)) (hx0 : x0 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 = h0 * (4 * q) + h1 * r0 + h2 * (5 * q))
    (hu : u0 + 2 ^ 64 * c1 = y0 + x1) (hu0 : u0 < 2 ^ 64)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      x0 + 5 * ((y1 + h2 * r0 + c1) / 4) + 2 ^ 64 * u0 + 2 ^ 128 * ((y1 + h2 * r0 + c1) % 4))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) :
    (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) % P =
      ((h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2) * (r0 + 2 ^ 64 * (4 * q))) % P ∧ w2 ≤ 4 := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := absorb_bounds hh0 hh1 hh2 hr0 hq
  have e5 : h1 * (5 * q) = 5 * (h1 * q) := by ring
  have e4 : h0 * (4 * q) = 4 * (h0 * q) := by ring
  have e5' : h2 * (5 * q) = 5 * (h2 * q) := by ring
  rw [expand]
  refine ⟨?_, ?_⟩
  · rw [show h0 * r0 + 2 ^ 64 * (h0 * (4 * q)) + 2 ^ 64 * (h1 * r0) + 2 ^ 130 * (h1 * q) +
        2 ^ 128 * (h2 * r0) + 2 ^ 194 * (h2 * q) =
        (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) +
          P * ((y1 + h2 * r0 + c1) / 4 + h1 * q + 2 ^ 64 * (h2 * q)) by
      simp only [P]; omega, Nat.add_mul_mod_self_left]
  · omega

/-- Adding a block `m0 + 2⁶⁴ m1 + 2¹²⁸ pad` to `h` with `h2 ≤ 4`: the result's
top word is at most 6. -/
theorem add_arith {h0 h1 h2 m0 m1 pad w0 w1 w2 : Nat} (hh0 : h0 < 2 ^ 64) (hh1 : h1 < 2 ^ 64)
    (hh2 : h2 ≤ 4) (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hpad : pad ≤ 1)
    (hw : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 =
      h0 + 2 ^ 64 * h1 + 2 ^ 128 * h2 + (m0 + 2 ^ 64 * m1 + 2 ^ 128 * pad))
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) : w2 ≤ 6 := by
  omega

end VG.Proof.Poly1305.X86_64
