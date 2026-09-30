import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305: Horner's rule in four lanes

Untrusted: everything here is checked by Lean. A vector implementation can
absorb four blocks at a time in four lanes: lane `k` holds `V_k`, and a group
of blocks `m₀ … m₃` makes it `(V_k + m_k) r⁴`; at the end, the last group
makes it `(V_k + m_k) r^(4-k)` and the lanes are summed. With
`S = r⁴ V₀ + r³ V₁ + r² V₂ + r V₃`, the invariant is `S ≡ r⁴ a` for the
accumulator `a` of the blocks so far (starting with `V₀ = a`, the others 0).
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)

/-- The value of a block with its `0x01` byte appended. -/
abbrev mv (b : List Byte) : Nat := leNum (b ++ [0x01])

theorem mod_step {x y : Nat} (r v : Nat) (h : x ≡ y [MOD P]) : r * (x + v) % P ≡ r * (y + v) [MOD P] :=
  (Nat.mod_modEq _ _).trans ((h.add_right v).mul_left r)

theorem absorbAll_four {r a : Nat} {b0 b1 b2 b3 : List Byte} (h0 : b0.length = 16) (h1 : b1.length = 16)
    (h2 : b2.length = 16) (h3 : b3.length = 16) :
    absorbAll r a (b0 ++ b1 ++ b2 ++ b3) ≡
      r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3 [MOD P] := by
  have l0 : (b0 ++ b1).length % 16 = 0 := by simp [h0, h1]
  have l1 : (b0 ++ b1 ++ b2).length % 16 = 0 := by simp [h0, h1, h2]
  rw [absorbAll_append l1, absorbAll_append l0, absorbAll_append (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega),
    absorbAll_block (by omega) (by omega), absorbAll_block (by omega) (by omega)]
  refine (mod_step r _ (mod_step r _ (mod_step r _ (Nat.mod_modEq _ _)))).trans ?_
  rw [show r * (r * (r * (r * (a + mv b0) + mv b1) + mv b2) + mv b3) =
    r ^ 4 * a + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3 by ring]

/-- The lanes' sum, weighted by the powers of `r` of the last group. -/
abbrev lanes (r V0 V1 V2 V3 : Nat) : Nat := r ^ 4 * V0 + r ^ 3 * V1 + r ^ 2 * V2 + r * V3

section
variable {r X V0 V1 V2 V3 W0 W1 W2 W3 : Nat} {b0 b1 b2 b3 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (hS : lanes r V0 V1 V2 V3 ≡ r ^ 4 * X [MOD P])
include h0 h1 h2 h3 hS

/-- A group of four blocks, each lane multiplied by `r⁴`. -/
theorem horner_step (e0 : W0 ≡ (V0 + mv b0) * r ^ 4 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 4 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 4 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r ^ 4 [MOD P]) :
    lanes r W0 W1 W2 W3 ≡ r ^ 4 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := (absorbAll_four (r := r) (a := X) h0 h1 h2 h3).mul_left (r ^ 4)
  have hL : lanes r W0 W1 W2 W3 ≡ r ^ 4 * (lanes r V0 V1 V2 V3 +
      (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) [MOD P] := by
    refine ((((e0.mul_left _).add (e1.mul_left _)).add (e2.mul_left _)).add (e3.mul_left _)).trans ?_
    rw [show r ^ 4 * ((V0 + mv b0) * r ^ 4) + r ^ 3 * ((V1 + mv b1) * r ^ 4) +
        r ^ 2 * ((V2 + mv b2) * r ^ 4) + r * ((V3 + mv b3) * r ^ 4) =
        r ^ 4 * (lanes r V0 V1 V2 V3 + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) by
      simp only [lanes]; ring]
  calc lanes r W0 W1 W2 W3
      _ ≡ r ^ 4 * (lanes r V0 V1 V2 V3 +
          (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) [MOD P] := hL
      _ ≡ r ^ 4 * (r ^ 4 * X + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)) [MOD P] :=
        (hS.add_right _).mul_left _
      _ = r ^ 4 * (r ^ 4 * X + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) := by ring
      _ ≡ r ^ 4 * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

/-- The last group, lane `k` multiplied by `r^(4-k)`, and the lanes summed. -/
theorem horner_last (e0 : W0 ≡ (V0 + mv b0) * r ^ 4 [MOD P]) (e1 : W1 ≡ (V1 + mv b1) * r ^ 3 [MOD P])
    (e2 : W2 ≡ (V2 + mv b2) * r ^ 2 [MOD P]) (e3 : W3 ≡ (V3 + mv b3) * r [MOD P]) :
    W0 + W1 + W2 + W3 ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := absorbAll_four (r := r) (a := X) h0 h1 h2 h3
  refine (((e0.add e1).add e2).add e3).trans ?_
  rw [show (V0 + mv b0) * r ^ 4 + (V1 + mv b1) * r ^ 3 + (V2 + mv b2) * r ^ 2 + (V3 + mv b3) * r =
    lanes r V0 V1 V2 V3 + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) by
      simp only [lanes]; ring]
  calc lanes r V0 V1 V2 V3 + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3)
      _ ≡ r ^ 4 * X + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) [MOD P] :=
        hS.add_right _
      _ = r ^ 4 * X + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3 := by ring
      _ ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

end

end VG.Proof.Poly1305
