import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305 in 26-bit limbs

The arithmetic of vector implementations that keep numbers modulo `p` in five
limbs of 26 bits (`x₀ + 2²⁶ x₁ + … + 2¹⁰⁴ x₄`), as Nat identities with no
bounds: the products `d_j` of two such numbers, with the terms that pass
`2¹³⁰` folded back times 5, and their carrying; how a block's two words split
into limbs; the final reduction; and the interleaved Horner evaluation of four
lanes. Each function sums in the order the code does, so that the terms the
code computes are these functions by definition.
-/

namespace VG.Proof.Poly1305.Limbs26

open VG.Spec.Poly1305 (P)

/-- The number whose limbs are `a 0`, …, `a 4` (of any size). -/
def val (a : Nat → Nat) : Nat := a 0 + 2 ^ 26 * a 1 + 2 ^ 52 * a 2 + 2 ^ 78 * a 3 + 2 ^ 104 * a 4

theorem P_eq : P = 1361129467683753853853498429727072845819 := by decide

/-! ## Products -/

/-- The products `d_j = 5 Σ_{i > j} a_i b_(5+j-i) + Σ_{i ≤ j} a_i b_(j-i)`,
summed as the code does (`s + s · 2²` is `5 s`). -/
def pd (a b : Nat → Nat) : Nat → Nat
  | 0 => let s := a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1; s + s * 2 ^ 2 + a 0 * b 0
  | 1 => let s := a 2 * b 4 + a 3 * b 3 + a 4 * b 2; s + s * 2 ^ 2 + a 0 * b 1 + a 1 * b 0
  | 2 => let s := a 3 * b 4 + a 4 * b 3; s + s * 2 ^ 2 + a 0 * b 2 + a 1 * b 1 + a 2 * b 0
  | 3 => let s := a 4 * b 4; s + s * 2 ^ 2 + a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0
  | _ => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0

/-- What the products leave out: the terms past `2¹³⁰`, over `2¹³⁰`. -/
def pc (a b : Nat → Nat) : Nat :=
  (a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1) + 2 ^ 26 * (a 2 * b 4 + a 3 * b 3 + a 4 * b 2) +
    2 ^ 52 * (a 3 * b 4 + a 4 * b 3) + 2 ^ 78 * (a 4 * b 4)

theorem pd_val (a b : Nat → Nat) : val (pd a b) + P * pc a b = val a * val b := by
  simp only [val, pd, pc, P_eq]
  ring

/-! ## Carrying -/

section
variable (d : Nat → Nat)

/-- The limbs carried from `d₀` up: `e₁ = d₁ + d₀ / 2²⁶`, … -/
def e1 : Nat := d 1 + d 0 / 2 ^ 26
def e2 : Nat := d 2 + e1 d / 2 ^ 26
def e3 : Nat := d 3 + e2 d / 2 ^ 26
def e4 : Nat := d 4 + e3 d / 2 ^ 26
/-- `d₄`'s carry, times 5 (`c + c · 2²`), added to `d₀`'s low bits. -/
def g0 (M : Nat) : Nat := (d 0 &&& M) + (e4 d / 2 ^ 26 + e4 d / 2 ^ 26 * 2 ^ 2)

/-- The limbs after carrying, with the mask `M = 2²⁶ - 1`. -/
def carry (M : Nat) : Nat → Nat
  | 0 => g0 d M &&& M
  | 1 => (e1 d &&& M) + g0 d M / 2 ^ 26
  | 2 => e2 d &&& M
  | 3 => e3 d &&& M
  | _ => e4 d &&& M

end

theorem and_mask (x : Nat) : x &&& 0x3ffffff = x % 2 ^ 26 := by
  rw [show (0x3ffffff : Nat) = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem carry_val (d : Nat → Nat) : val (carry d 0x3ffffff) + P * (e4 d / 2 ^ 26) = val d := by
  simp only [val, carry, g0, e4, e3, e2, e1, and_mask, P_eq]
  omega

/-- The product of two numbers, carried. -/
def mul (a b : Nat → Nat) : Nat → Nat := carry (pd a b) 0x3ffffff

theorem mul_mod (a b : Nat → Nat) : val (mul a b) % P = val a * val b % P := by
  have h₁ := carry_val (pd a b)
  have h₂ := pd_val a b
  rw [← h₂, ← h₁, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, mul]

/-! ## Splitting words into limbs

The limbs of `lo + 2⁶⁴ hi` (`lo < 2⁶⁴`), as the code splits them, are
`lo << 38 >> 38`, `lo << 12 >> 38`, `hi << 50 >> 38 | lo >> 52`,
`hi << 24 >> 38` and `hi >> 40`. (They are stated inline rather than as
definitions: `rfl` against a definition whose body is a division unfolds
the division, very slowly.) -/

theorem split_or {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    (hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| lo / 2 ^ 52) = 2 ^ 12 * (hi % 2 ^ 14) + lo / 2 ^ 52 := by
  rw [show hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 = 2 ^ 12 * (hi % 2 ^ 14) by omega,
    ← Nat.two_pow_add_eq_or_of_lt (show lo / 2 ^ 52 < 2 ^ 12 by omega)]

theorem split_val {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    lo * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 + 2 ^ 26 * (lo * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) +
      2 ^ 52 * (hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| lo / 2 ^ 52) + 2 ^ 78 * (hi * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) +
      2 ^ 104 * (hi / 2 ^ 40) = lo + 2 ^ 64 * hi := by
  rw [split_or hlo]
  omega

/-! ## The final reduction -/

section
variable (c : Nat → Nat) (M five mk : Nat)

/-- `h₁` to `h₄` carried, with the mask `M`. -/
def f2' : Nat := c 2 + c 1 / 2 ^ 26
def f3' : Nat := c 3 + f2' c / 2 ^ 26
def fc : Nat → Nat
  | 0 => c 0
  | 1 => c 1 &&& M
  | 2 => f2' c &&& M
  | 3 => f3' c &&& M
  | _ => c 4 + f3' c / 2 ^ 26

/-- `g = h + 5`, carried (before its limbs are masked). -/
def g0' : Nat := fc c M 0 + five
def g1' : Nat := fc c M 1 + g0' c M five / 2 ^ 26
def g2' : Nat := fc c M 2 + g1' c M five / 2 ^ 26
def g3' : Nat := fc c M 3 + g2' c M five / 2 ^ 26
def g4' : Nat := fc c M 4 + g3' c M five / 2 ^ 26
def gl : Nat → Nat
  | 0 => g0' c M five
  | 1 => g1' c M five
  | 2 => g2' c M five
  | 3 => g3' c M five
  | _ => g4' c M five

/-- The select mask: `(g₄ >> 26) · mk`, as `vpmuludq` computes it. -/
def sel : Nat := g4' c M five / 2 ^ 26 % 2 ^ 32 * (mk % 2 ^ 32)

/-- `h mod p`, limb by limb. -/
def fin (i : Nat) : Nat :=
  ((2 ^ 64 - 1 - sel c M five mk) &&& fc c M i) ||| (gl c M five i &&& M &&& sel c M five mk)

end

theorem and_high_zero {x : Nat} (hx : x < 2 ^ 27) : (2 ^ 64 - 1 - (2 ^ 27 - 1)) &&& x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 27
  · rw [show 2 ^ 64 - 1 - (2 ^ 27 - 1) = (2 ^ 37 - 1) * 2 ^ 27 by decide, Nat.testBit_mul_two_pow,
      decide_eq_false (by omega), Bool.false_and, Bool.false_and]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.and_false]

theorem fin_val {c : Nat → Nat} (h0 : c 0 < 2 ^ 26) (h1 : c 1 < 2 ^ 27) (h2 : c 2 < 2 ^ 26)
    (h3 : c 3 < 2 ^ 26) (h4 : c 4 < 2 ^ 26) :
    val (fin c 0x3ffffff 5 0x7ffffff) = val c % P ∧ ∀ i < 5, fin c 0x3ffffff 5 0x7ffffff i < 2 ^ 26 := by
  have ef : ∀ i < 5, fc c 0x3ffffff i = (if i = 0 then c 0 else if i = 1 then c 1 % 2 ^ 26
      else if i = 2 then f2' c % 2 ^ 26 else if i = 3 then f3' c % 2 ^ 26 else c 4 + f3' c / 2 ^ 26) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [fc, and_mask] <;> rfl
  have e2 : f2' c = c 2 + c 1 / 2 ^ 26 := rfl
  have e3 : f3' c = c 3 + f2' c / 2 ^ 26 := rfl
  -- The limbs of `h` carried, and of `g = h + 5`.
  obtain ⟨F0, F1, F2, F3, F4⟩ : fc c 0x3ffffff 0 = c 0 ∧ fc c 0x3ffffff 1 = c 1 % 2 ^ 26 ∧
      fc c 0x3ffffff 2 = f2' c % 2 ^ 26 ∧ fc c 0x3ffffff 3 = f3' c % 2 ^ 26 ∧
      fc c 0x3ffffff 4 = c 4 + f3' c / 2 ^ 26 :=
    ⟨ef 0 (by decide), ef 1 (by decide), ef 2 (by decide), ef 3 (by decide), ef 4 (by decide)⟩
  have G0 : g0' c 0x3ffffff 5 = c 0 + 5 := by rw [g0', F0]
  have G1 : g1' c 0x3ffffff 5 = c 1 % 2 ^ 26 + (c 0 + 5) / 2 ^ 26 := by rw [g1', F1, G0]
  have G2 : g2' c 0x3ffffff 5 = f2' c % 2 ^ 26 + g1' c 0x3ffffff 5 / 2 ^ 26 := by rw [g2', F2]
  have G3 : g3' c 0x3ffffff 5 = f3' c % 2 ^ 26 + g2' c 0x3ffffff 5 / 2 ^ 26 := by rw [g3', F3]
  have G4 : g4' c 0x3ffffff 5 = c 4 + f3' c / 2 ^ 26 + g3' c 0x3ffffff 5 / 2 ^ 26 := by rw [g4', F4]
  have gl_eq : ∀ i < 5, gl c 0x3ffffff 5 i &&& 0x3ffffff = (if i = 0 then g0' c 0x3ffffff 5
      else if i = 1 then g1' c 0x3ffffff 5 else if i = 2 then g2' c 0x3ffffff 5
      else if i = 3 then g3' c 0x3ffffff 5 else g4' c 0x3ffffff 5) % 2 ^ 26 := by
    intro i hi
    rw [and_mask]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hs : sel c 0x3ffffff 5 0x7ffffff = g4' c 0x3ffffff 5 / 2 ^ 26 * (2 ^ 27 - 1) := by
    rw [sel, show (0x7ffffff : Nat) % 2 ^ 32 = 2 ^ 27 - 1 by decide]
    congr 1
    rw [G4, G3, G2, G1, e3, e2]
    omega
  have hq : g4' c 0x3ffffff 5 / 2 ^ 26 = 0 ∨ g4' c 0x3ffffff 5 / 2 ^ 26 = 1 := by
    rw [G4, G3, G2, G1, e3, e2]; omega
  have fin_eq : ∀ i < 5, fin c 0x3ffffff 5 0x7ffffff i =
      if g4' c 0x3ffffff 5 / 2 ^ 26 = 0 then fc c 0x3ffffff i else gl c 0x3ffffff 5 i &&& 0x3ffffff := by
    intro i hi
    have hf : fc c 0x3ffffff i < 2 ^ 27 := by
      rw [ef i hi]
      rw [e3, e2]
      split <;> [omega; split <;> [omega; split <;> [omega; split <;> omega]]]
    rw [fin, hs]
    rcases hq with hq | hq <;> rw [hq]
    · simp only [Nat.zero_mul, Nat.sub_zero, Nat.and_zero, Nat.or_zero, ite_true]
      rw [show (2 ^ 64 - 1 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_comm,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.lt_trans hf (by decide))]
    · simp only [Nat.one_mul, and_high_zero hf, Nat.zero_or, show (1 : Nat) ≠ 0 by decide, ite_false]
      rw [Nat.and_two_pow_sub_one_eq_mod, and_mask]
      omega
  have H := G4
  rw [G3, G2, G1, e3, e2] at H
  rw [e3] at F4 F3
  rw [e2] at F4 F3 F2
  rcases hq with hq | hq
  · have e : ∀ i < 5, fin c 0x3ffffff 5 0x7ffffff i = fc c 0x3ffffff i := fun i hi => by
      rw [fin_eq i hi, ite_eq_left hq]
    rw [H] at hq
    refine ⟨?_, fun i hi => ?_⟩
    · rw [val, val, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
        F0, F1, F2, F3, F4, P_eq]
      omega
    · rw [e i hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [F0]; omega
      · rw [F1]; omega
      · rw [F2]; omega
      · rw [F3]; omega
      · rw [F4]; omega
  · have e : ∀ i < 5, fin c 0x3ffffff 5 0x7ffffff i = gl c 0x3ffffff 5 i &&& 0x3ffffff := fun i hi => by
      rw [fin_eq i hi, ite_eq_right (by omega)]
    rw [H] at hq
    refine ⟨?_, fun i hi => ?_⟩
    · rw [val, val, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
        gl_eq 0 (by decide), gl_eq 1 (by decide), gl_eq 2 (by decide), gl_eq 3 (by decide),
        gl_eq 4 (by decide)]
      simp only [ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (3 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
        show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide]
      rw [H, G3, G2, G1, G0, e3, e2, P_eq]
      omega
    · rw [e i hi, and_mask]; omega

/-! ## Words -/

section
variable (o : Nat → Nat)

/-- The three words of `h`, as `storeH` computes them. -/
def w0 : Nat := o 1 * 2 ^ 26 % 2 ^ 64 ||| o 0 ||| o 2 * 2 ^ 52 % 2 ^ 64
def w1 : Nat := o 2 / 2 ^ 12 ||| o 3 * 2 ^ 14 % 2 ^ 64 ||| o 4 * 2 ^ 40 % 2 ^ 64

end

theorem words_val {o : Nat → Nat} (h : ∀ i < 5, o i < 2 ^ 26) :
    w0 o + 2 ^ 64 * w1 o + 2 ^ 128 * (o 4 / 2 ^ 24) = val o ∧ w0 o < 2 ^ 64 ∧ w1 o < 2 ^ 64 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have e0 : w0 o = 2 ^ 52 * (o 2 % 2 ^ 12) + (2 ^ 26 * o 1 + o 0) := by
    have a1 : (o 1 * 2 ^ 26 % 2 ^ 64 ||| o 0) = 2 ^ 26 * o 1 + o 0 := by
      rw [show o 1 * 2 ^ 26 % 2 ^ 64 = 2 ^ 26 * o 1 by omega]
      exact (Nat.two_pow_add_eq_or_of_lt h0 _).symm
    rw [w0, a1, show o 2 * 2 ^ 52 % 2 ^ 64 = 2 ^ 52 * (o 2 % 2 ^ 12) by omega, Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  have e1 : w1 o = 2 ^ 40 * (o 4 % 2 ^ 24) + (2 ^ 14 * o 3 + o 2 / 2 ^ 12) := by
    have b1 : (o 2 / 2 ^ 12 ||| o 3 * 2 ^ 14 % 2 ^ 64) = 2 ^ 14 * o 3 + o 2 / 2 ^ 12 := by
      rw [show o 3 * 2 ^ 14 % 2 ^ 64 = 2 ^ 14 * o 3 by omega, Nat.or_comm]
      exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
    rw [w1, b1, show o 4 * 2 ^ 40 % 2 ^ 64 = 2 ^ 40 * (o 4 % 2 ^ 24) by omega, Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  simp only [e0, e1, val]
  omega

end VG.Proof.Poly1305.Limbs26
