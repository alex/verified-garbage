import VerifiedGarbage.Proof.Poly1305.Horner

/-!
# Poly1305: Horner's rule in eight lanes

Untrusted: everything here is checked by Lean. As `Horner.lean`, with eight
lanes: lane `j` holds `V_j`, a group of blocks `m₀ … m₇` makes it
`(V_j + m_j) r⁸`, and the last group `(V_j + m_j) r^(8-j)`, after which the
lanes are summed. With `S = r⁸ V₀ + r⁷ V₁ + … + r V₇`, the invariant is
`S ≡ r⁸ a` for the accumulator `a` of the blocks so far.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

section
variable {r a : Nat} {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
include h0 h1 h2 h3 h4 h5 h6 h7

theorem absorbAll_eight :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
        r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 [MOD P] := by
  have l : (b0 ++ b1 ++ b2 ++ b3).length % 16 = 0 := by simp [h0, h1, h2, h3]
  rw [show b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 = (b0 ++ b1 ++ b2 ++ b3) ++ (b4 ++ b5 ++ b6 ++ b7) by
    simp only [List.append_assoc], absorbAll_append l]
  refine (absorbAll_four h4 h5 h6 h7).trans ?_
  have hA := absorbAll_four (r := r) (a := a) h0 h1 h2 h3
  refine ((((hA.mul_left (r ^ 4)).add_right _).add_right _).add_right _).add_right _ |>.trans ?_
  rw [show r ^ 4 * (r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 =
    r ^ 8 * a + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 by ring]

end

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes8 (r V0 V1 V2 V3 V4 V5 V6 V7 : Nat) : Nat :=
  r ^ 8 * V0 + r ^ 7 * V1 + r ^ 6 * V2 + r ^ 5 * V3 + r ^ 4 * V4 + r ^ 3 * V5 + r ^ 2 * V6 + r * V7

/-- The weighted values of a group's blocks. -/
abbrev msum8 (r : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : List Byte) : Nat :=
  r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 + r ^ 3 * mv b5 +
    r ^ 2 * mv b6 + r * mv b7

section
variable {r X V0 V1 V2 V3 V4 V5 V6 V7 W0 W1 W2 W3 W4 W5 W6 W7 : Nat}
  {b0 b1 b2 b3 b4 b5 b6 b7 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (h4 : b4.length = 16) (h5 : b5.length = 16) (h6 : b6.length = 16) (h7 : b7.length = 16)
  (hS : lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 ≡ r ^ 8 * X [MOD P])
include h0 h1 h2 h3 h4 h5 h6 h7 hS

omit hS in
theorem absorbAll_eight' :
    absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) ≡
      r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 [MOD P] := by
  refine (absorbAll_eight h0 h1 h2 h3 h4 h5 h6 h7).trans ?_
  rw [show r ^ 8 * X + r ^ 8 * mv b0 + r ^ 7 * mv b1 + r ^ 6 * mv b2 + r ^ 5 * mv b3 + r ^ 4 * mv b4 +
      r ^ 3 * mv b5 + r ^ 2 * mv b6 + r * mv b7 = r ^ 8 * X + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [msum8]; ring]

/-- A group of eight blocks, each lane multiplied by `r⁸`. -/
theorem horner8_step (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 8 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 8 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 8 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 8 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 8 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 8 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r ^ 8 [MOD P]) :
    lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := (absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7).mul_left (r ^ 8)
  have hL : lanes8 r W0 W1 W2 W3 W4 W5 W6 W7 ≡
      r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) [MOD P] := by
    refine ((((((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).add
      (e4.mul_left _)).add (e5.mul_left _)).add (e6.mul_left _)).add (e7.mul_left _)).trans ?_
    rw [show r ^ 8 * ((V0 + mv b0) * r ^ 8) + r ^ 7 * ((V1 + mv b1) * r ^ 8) +
        r ^ 6 * ((V2 + mv b2) * r ^ 8) + r ^ 5 * ((V3 + mv b3) * r ^ 8) + r ^ 4 * ((V4 + mv b4) * r ^ 8) +
        r ^ 3 * ((V5 + mv b5) * r ^ 8) + r ^ 2 * ((V6 + mv b6) * r ^ 8) + r * ((V7 + mv b7) * r ^ 8) =
        r ^ 8 * (lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7) by
      simp only [lanes8, msum8]; ring]
  exact hL.trans (((hS.add_right _).mul_left _).trans hA.symm)

/-- The last group, lane `j` multiplied by `r^(8-j)`, and the lanes summed. -/
theorem horner8_last (e0 : W0 ≡ (V0 + mv b0) * r ^ 8 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 7 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 6 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 5 [MOD P])
    (e4 : W4 ≡ (V4 + mv b4) * r ^ 4 [MOD P]) (e5 : W5 ≡ (V5 + mv b5) * r ^ 3 [MOD P])
    (e6 : W6 ≡ (V6 + mv b6) * r ^ 2 [MOD P]) (e7 : W7 ≡ (V7 + mv b7) * r [MOD P]) :
    W0 + W1 + W2 + W3 + W4 + W5 + W6 + W7 ≡
      absorbAll r X (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) [MOD P] := by
  have hA := absorbAll_eight' (r := r) (X := X) h0 h1 h2 h3 h4 h5 h6 h7
  refine (((((((e0.add e1).add e2).add e3).add e4).add e5).add e6).add e7).trans ?_
  rw [show (V0 + mv b0) * r ^ 8 + (V1 + mv b1) * r ^ 7 + (V2 + mv b2) * r ^ 6 + (V3 + mv b3) * r ^ 5 +
      (V4 + mv b4) * r ^ 4 + (V5 + mv b5) * r ^ 3 + (V6 + mv b6) * r ^ 2 + (V7 + mv b7) * r =
      lanes8 r V0 V1 V2 V3 V4 V5 V6 V7 + msum8 r b0 b1 b2 b3 b4 b5 b6 b7 by
    simp only [lanes8, msum8]; ring]
  exact (hS.add_right _).trans hA.symm

end

end VG.Proof.Poly1305
