import VerifiedGarbage.Proof.Gcm.X86_64.Ctmul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs

/-!
# GHASH on x86-64: Karatsuba, the reduction and `x⁻¹ · H`

Untrusted: everything here is checked by Lean. In the ring `Q` of
`Proof/Gcm/Poly.lean`, with `ψ w` the class of a 64-bit word (the
coefficients of `x⁰ … x⁶³`):

* the three word products of a block give `x · Y · H'` as four words
  (`ψ_karatsuba`);
* `fold` adds `x¹²⁸ · w` to two words as `x⁰ … x¹²⁷` (`ψ_fold`), so the
  reduction keeps the class (`φ_reduce`);
* `hInv` computes `H' = x⁻¹ · H` (`x_φ_hInv`);

hence one block computes `(Y ⊕ X) • H` (`reduce_eq_mul`).
-/

namespace VG.Proof.Gcm.X86_64.Ctmul

open Polynomial VG.Proof.Gcm.Poly

/-- The class of a word. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem ψ_xor (a b : BitVec 64) : ψ (a ^^^ b) = ψ a + ψ b := by
  simp only [ψ, gp_xor, map_add]

theorem φ_append (a b : BitVec 64) : φ (a ++ b) = ψ a + x ^ 64 * ψ b := by
  simp only [φ, ψ, gp_append, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

/-- A word product. -/
theorem ψ_prodVal {hv yv rh rl : BitVec 64} (h : rh ++ rl = prodVal hv yv) :
    ψ rh + x ^ 64 * ψ rl = x * ψ hv * ψ yv := by
  rw [← φ_append, h]
  simp only [φ, ψ, gp_prodVal, map_mul, AdjoinRoot.mk_X]

/-! ## Karatsuba -/

/-- The four words of `x · Y · H` from the products `A = Y_A · H_A`,
`B = Y_B · H_B` and `M = (Y_A ⊕ Y_B) · (H_A ⊕ H_B)`, as `Impl.Gcm.X86_64.body`
adds them. -/
theorem ψ_karatsuba {yA yB hA hB al ah bl bh ml mh : BitVec 64}
    (hA' : ah ++ al = prodVal hA yA) (hB' : bh ++ bl = prodVal hB yB)
    (hM : mh ++ ml = prodVal (hA ^^^ hB) (yA ^^^ yB)) :
    ψ ah + x ^ 64 * ψ (((al ^^^ bh) ^^^ ah) ^^^ mh) +
      x ^ 128 * ψ (((al ^^^ bh) ^^^ bl) ^^^ ml) + x ^ 192 * ψ bl =
      x * φ (yA ++ yB) * φ (hA ++ hB) := by
  have eA := ψ_prodVal hA'
  have eB := ψ_prodVal hB'
  have eM := ψ_prodVal hM
  simp only [ψ_xor] at eM ⊢
  simp only [φ_append]
  linear_combination eA + x ^ 64 * (eA + eB + eM) + x ^ 128 * eB +
    x ^ 65 * (ψ hA * ψ yA + ψ hB * ψ yB) * two_Q

/-! ## The reduction -/

theorem gp_shr_shl (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) :
    gp (w >>> s) + X ^ 64 * gp (w <<< (64 - s)) = X ^ s * gp w := by
  ext d
  rw [coeff_add, coeff_gp, coeff_X_pow_mul', coeff_X_pow_mul', coeff_gp, coeff_gp,
    BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  by_cases h1 : s ≤ d
  · by_cases h2 : 64 ≤ d
    · simp only [ite_eq_left h1, ite_eq_left h2, decide_eq_false (show ¬ d < 64 by omega),
        Bool.false_and, show d - 64 + (64 - s) = d - s by omega]
      simp [bit]
    · simp only [ite_eq_left h1, ite_eq_right h2, decide_eq_true (show d < 64 by omega),
        decide_eq_false (show ¬ d < s by omega), Bool.not_false, Bool.true_and, add_zero]
  · simp only [ite_eq_right h1, ite_eq_right (show ¬ 64 ≤ d by omega),
      decide_eq_true (show d < s by omega), Bool.not_true, Bool.false_and, Bool.and_false, add_zero]
    rfl

theorem ψ_shr_shl (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) :
    ψ (w >>> s) + x ^ 64 * ψ (w <<< (64 - s)) = x ^ s * ψ w := by
  have := congrArg (AdjoinRoot.mk g) (gp_shr_shl w hs hs')
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at this
  exact this

/-- What `fold` adds to the lower word. -/
def foldLo (lo w : BitVec 64) : BitVec 64 := (((lo ^^^ w) ^^^ (w >>> 1)) ^^^ (w >>> 2)) ^^^ (w >>> 7)

/-- … and to the higher. -/
def foldHi (hi w : BitVec 64) : BitVec 64 := ((hi ^^^ (w <<< 63)) ^^^ (w <<< 62)) ^^^ (w <<< 57)

theorem ψ_fold (lo hi w : BitVec 64) :
    ψ (foldLo lo w) + x ^ 64 * ψ (foldHi hi w) = ψ lo + x ^ 64 * ψ hi + x ^ 128 * ψ w := by
  have e1 := ψ_shr_shl w (s := 1) (by omega) (by omega)
  have e2 := ψ_shr_shl w (s := 2) (by omega) (by omega)
  have e7 := ψ_shr_shl w (s := 7) (by omega) (by omega)
  simp only [foldLo, foldHi, ψ_xor]
  simp only [Nat.reduceSub] at e1 e2 e7
  linear_combination e1 + e2 + e7 - ψ w * x128

/-- The reduction: `W₃` into `W₁, W₂`, then `W₂` into `W₀, W₁`. -/
def reduce (w0 w1 w2 w3 : BitVec 64) : BitVec 128 :=
  foldLo w0 (foldHi w2 w3) ++ foldHi (foldLo w1 w3) (foldHi w2 w3)

theorem φ_reduce (w0 w1 w2 w3 : BitVec 64) :
    φ (reduce w0 w1 w2 w3) = ψ w0 + x ^ 64 * ψ w1 + x ^ 128 * ψ w2 + x ^ 192 * ψ w3 := by
  rw [reduce, φ_append, ψ_fold]
  have := ψ_fold w1 w2 w3
  linear_combination x ^ 64 * this

/-! ## `x⁻¹ · H` -/

/-- `x⁻¹ = 1 + x + x⁶ + x¹²⁷`. -/
abbrev xInv : BitVec 128 := Impl.Gcm.X86_64.xInvHigh ++ (1 : BitVec 64)

theorem gp_xInv : gp xInv = 1 + X + X ^ 6 + X ^ 127 := by
  have hb : ∀ d < 128, xInv.getMsbD d = (d = 0 || d = 1 || d = 6 || d = 127) := by decide
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 127 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h6, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp [bit, h0, h1, h6, h7, show (1 : Nat) ≠ d from fun h => h1 h.symm]
  · have e : xInv.getMsbD d = false := BitVec.getMsbD_of_ge _ _ (by omega)
    rw [e]
    simp [bit, show d ≠ 6 by omega, show (1 : Nat) ≠ d by omega, show d ≠ 0 by omega,
      show d ≠ 127 by omega]

theorem x_φ_xInv : x * φ xInv = 1 := by
  simp only [φ, gp_xInv, map_add, map_one, map_pow, AdjoinRoot.mk_X]
  linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q

theorem gp_shl1 (h : BitVec 128) : X * gp (h <<< 1) + C (bit (h.getMsbD 0)) = gp h := by
  ext d
  rw [coeff_add, coeff_C, coeff_gp]
  rcases d with _ | d
  · simp
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]; simp

/-- `hInv`'s result is `x⁻¹ · H`. -/
theorem x_φ_hInv (h : BitVec 128) :
    x * φ ((h <<< 1) ^^^ (if h.getMsbD 0 then xInv else 0)) = φ h := by
  have e := congrArg (AdjoinRoot.mk g) (gp_shl1 h)
  simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at e
  rw [φ_xor, mul_add]
  change x * AdjoinRoot.mk g (gp (h <<< 1)) + _ = AdjoinRoot.mk g (gp h)
  rw [← e]
  split_ifs with hb
  · rw [x_φ_xInv, hb]; simp [bit]
  · rw [φ_zero, Bool.not_eq_true] at *; rw [hb]; simp [bit]

/-! ## One block -/

/-- A block multiplied by `x⁻¹ · H` with the three word products, and
reduced, is its product with `H`. -/
theorem reduce_eq_mul {yA yB hA hB al ah bl bh ml mh : BitVec 64} {H : BitVec 128}
    (hH : x * φ (hA ++ hB) = φ H)
    (hA' : ah ++ al = prodVal hA yA) (hB' : bh ++ bl = prodVal hB yB)
    (hM : mh ++ ml = prodVal (hA ^^^ hB) (yA ^^^ yB)) :
    reduce ah (((al ^^^ bh) ^^^ ah) ^^^ mh) (((al ^^^ bh) ^^^ bl) ^^^ ml) bl =
      Spec.Gcm.mul (yA ++ yB) H := by
  apply φ_inj
  rw [φ_reduce, ψ_karatsuba hA' hB' hM, φ_mul, ← hH]
  ring

end VG.Proof.Gcm.X86_64.Ctmul
