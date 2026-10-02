import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# GHASH with PMULL: the arithmetic

What the instructions of `Impl.Gcm.AArch64.Pmull` compute, in the ring `Q` of
`Proof/Gcm/Poly.lean` (as `Proof/Gcm/X86_64/Pclmul/Ghash.lean` does for
PCLMULQDQ):

* `pmull` multiplies polynomials (`φ_polyMul`), so the four of `acc`
  compute `x · a · t` as a 256-bit value (`Prod.val_acc`), where `a` is a
  block as loaded (its halves swapped: its class is `ρ a`);
* `reduce` maps a 256-bit value to a block of the same class, with its
  halves swapped (`ρ_reduce`);
* `rev64 .16b` of a 16-byte load is the block as loaded (`ρ_load`), and
  undoes itself (`rev64b_rev64b`).
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open Polynomial
open VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (poly xInv2Hi)

/-! ## Carry-less multiplication -/

theorem gp_shl (b : BitVec 64) {j : Nat} (hj : j < 64) :
    gp ((b.setWidth 128) <<< j) = X ^ (64 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 64 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 128 - 64 ≤ d + j by omega), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [h, ite_false, decide_eq_false (show ¬ 128 - 64 ≤ d + j by omega), Bool.false_and]; rfl

/-- The first `k` steps of `polyMul`. -/
def clSteps (a b : BitVec 64) (k : Nat) : BitVec 128 :=
  (List.range k).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 128 <<< i) else acc) 0

theorem gp_clSteps (a b : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    gp (clSteps a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (63 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [clSteps, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : clSteps a b (k + 1) =
        if a.getLsbD k then clSteps a b k ^^^ (b.setWidth 128 <<< k) else clSteps a b k := by
      simp only [clSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega), gp_shl b (by omega),
        show 64 - k = 63 - k + 1 by omega, pow_succ]
      ring
    · rw [ih (by omega)]; ring

theorem gp_lsb (a : BitVec 64) :
    (∑ i ∈ Finset.range 64, if a.getLsbD i then (X : P) ^ (63 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega), Bool.true_and,
    show 64 - 1 - i = 63 - i by omega, show 63 - (64 - 1 - i) = i by omega]

/-- `pmull` multiplies polynomials (with the factor `X` of the reflected
representation). -/
theorem gp_polyMul (a b : BitVec 64) : gp (polyMul a b) = X * gp a * gp b := by
  rw [show polyMul a b = clSteps a b 64 from rfl, gp_clSteps a b (Nat.le_refl _), gp_lsb]

/-! ## Doublewords -/

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem φ_polyMul (a b : BitVec 64) : φ (polyMul a b) = x * ψ a * ψ b := by
  simp only [φ, ψ, gp_polyMul, map_mul, AdjoinRoot.mk_X]

theorem ψ_xor (a b : BitVec 64) : ψ (a ^^^ b) = ψ a + ψ b := by
  simp only [ψ, gp_xor, map_add]

theorem φ_append (a b : BitVec 64) : φ (a ++ b) = ψ a + x ^ 64 * ψ b := by
  simp only [φ, ψ, gp_append, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

theorem vdwords (v : BitVec 128) : v = vdword v 1 ++ vdword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, mul_zero, zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_append_0 (a b : BitVec 64) : vdword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, mul_zero, zero_add, ite_true]

theorem vdword_append_1 (a b : BitVec 64) : vdword (a ++ b) 1 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, mul_one, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem vdword_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword, BitVec.extractLsb'_xor]

theorem φ_v (v : BitVec 128) : φ v = ψ (vdword v 1) + x ^ 64 * ψ (vdword v 0) := by
  conv => lhs; rw [vdwords v]
  rw [φ_append]

/-- The class of a block as loaded (its halves swapped). -/
noncomputable def ρ (v : BitVec 128) : Q := ψ (vdword v 0) + x ^ 64 * ψ (vdword v 1)

theorem ρ_xor (a b : BitVec 128) : ρ (a ^^^ b) = ρ a + ρ b := by
  simp only [ρ, vdword_xor, ψ_xor]; ring

/-! ## `ext #8` -/

/-- `ext d, n, m, #8`: the high half of `n`, then the low half of `m`. -/
def ext8 (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> 64).extractLsb' 0 128

theorem ext8_eq (n m : BitVec 128) : ext8 n m = vdword m 0 ++ vdword n 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ext8, vdword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true, show 64 + i < 128 by omega, decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 64 + i < 128 by omega, decide_eq_true (show i - 64 < 64 by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem vdword_ext8_0 (n m : BitVec 128) : vdword (ext8 n m) 0 = vdword n 1 := by
  rw [ext8_eq, vdword_append_0]

theorem vdword_ext8_1 (n m : BitVec 128) : vdword (ext8 n m) 1 = vdword m 0 := by
  rw [ext8_eq, vdword_append_1]

theorem φ_ext8 (n m : BitVec 128) : φ (ext8 n m) = ψ (vdword m 0) + x ^ 64 * ψ (vdword n 1) := by
  rw [ext8_eq, φ_append]

/-- A block with its halves swapped, as loaded. -/
theorem ρ_ext8_self (v : BitVec 128) : ρ (ext8 v v) = φ v := by
  rw [ρ, vdword_ext8_0, vdword_ext8_1, φ_v]

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

/-- The four products of `acc`, of the block `a` as loaded and the key `t`
(`s` its halves swapped), added to `p`. -/
def acc (p : Prod) (a s t : BitVec 128) : Prod :=
  ⟨p.lo ^^^ polyMul (vdword a 1) (vdword s 1),
   p.mid ^^^ polyMul (vdword a 0) (vdword t 0) ^^^ polyMul (vdword a 1) (vdword t 1),
   p.hi ^^^ polyMul (vdword a 0) (vdword s 0)⟩

def zero : Prod := ⟨0, 0, 0⟩

theorem val_zero : zero.val = 0 := by
  simp only [val, zero, BitVec.ofNat_eq_ofNat, φ_zero', mul_zero, add_zero]

theorem val_acc (p : Prod) (a t : BitVec 128) :
    (p.acc a (ext8 t t) t).val = p.val + x * ρ a * φ t := by
  simp only [acc, val, φ_xor, vdword_ext8_0, vdword_ext8_1, φ_polyMul, ρ, φ_v t]
  ring

end Prod

/-! ## The reduction -/

theorem ψ_poly : ψ poly = 1 + x + x ^ 6 := by
  have hb : ∀ d < 64, poly.getMsbD d = (d = 0 || d = 1 || d = 6) := by decide +kernel
  have h : gp poly = 1 + X + X ^ 6 := by
    ext d
    rw [coeff_gp]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    by_cases hd : d < 64
    · rw [hb d hd]
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6)) with
        rfl | rfl | rfl | ⟨h0, h1, h6⟩
      · decide
      · decide
      · decide
      · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte,
          show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : poly.getMsbD d = false := by
        simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
        omega
      rw [e]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega,
        show (1 : Nat) ≠ d by omega, add_zero, show d ≠ 6 by omega]
  simp only [ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem φ_ext8_self (v : BitVec 128) : φ (ext8 v v) = ρ v := by rw [φ_ext8, ρ]

theorem ext8_ext8 (v : BitVec 128) : ext8 (ext8 v v) (ext8 v v) = v := by
  rw [ext8_eq (ext8 v v), vdword_ext8_0, vdword_ext8_1, ← vdwords]

/-- A block as loaded, plus the `pmull` of its low half by `0xc2 · 2⁵⁶`, is of
the class of `x⁶⁴` times the block. -/
theorem ρ_add_polyMul (u : BitVec 128) : ρ u + φ (polyMul (vdword u 0) poly) = x ^ 64 * φ u := by
  rw [ρ, φ_polyMul, ψ_poly, φ_v u]
  linear_combination (-ψ (vdword u 0)) * x128

/-- `fold(v) = swap(v) ⊕ pmull(v₀, 0xc2 · 2⁵⁶)` is of the class of `x⁶⁴ · v`. -/
theorem φ_fold (v : BitVec 128) : φ (ext8 v v ^^^ polyMul (vdword v 0) poly) = x ^ 64 * φ v := by
  rw [φ_xor, φ_ext8_self, ρ_add_polyMul]

/-- The block, with its halves swapped, that `reduce` computes from a product:
`swap(hi ⊕ fold(u)) = swap(hi) ⊕ u ⊕ swap(pmull(u₀, 0xc2 · 2⁵⁶))` for
`u = mid ⊕ fold(lo)`. -/
def reduce (p : Prod) : BitVec 128 :=
  let u := (p.mid ^^^ ext8 p.lo p.lo) ^^^ polyMul (vdword p.lo 0) poly
  (ext8 p.hi p.hi ^^^ u) ^^^ ext8 (polyMul (vdword u 0) poly) (polyMul (vdword u 0) poly)

theorem ρ_reduce (p : Prod) : ρ (reduce p) = p.val := by
  simp only [reduce]
  rw [ρ_xor, ρ_xor, ρ_ext8_self, ρ_ext8_self, add_assoc, ρ_add_polyMul, BitVec.xor_assoc, φ_xor,
    φ_fold, Prod.val]
  ring

/-! ## `x⁻²` -/

/-- `x⁻²` (reflected). -/
def xInv2 : BitVec 128 := xInv2Hi ++ 3#64

theorem gp_xInv2 : gp xInv2 = X + X ^ 5 + X ^ 6 + X ^ 126 + X ^ 127 := by
  have hb : ∀ d < 128, xInv2.getMsbD d = (d = 1 || d = 5 || d = 6 || d = 126 || d = 127) := by
    decide +kernel
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 1 ∨ d = 5 ∨ d = 6 ∨ d = 126 ∨ d = 127 ∨
      (d ≠ 1 ∧ d ≠ 5 ∧ d ≠ 6 ∧ d ≠ 126 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | rfl | ⟨h1, h5, h6, h126, h127⟩
    · decide
    · decide
    · decide
    · decide
    · decide
    · simp only [bit, h1, decide_false, h5, Bool.or_self, h6, h126, h127, Bool.false_eq_true,
        ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv2.getMsbD d = false := by
      simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d by omega, add_zero,
      show d ≠ 5 by omega, show d ≠ 6 by omega, show d ≠ 126 by omega, show d ≠ 127 by omega]

theorem x2_φ_xInv2 : x ^ 2 * φ xInv2 = 1 := by
  simp only [φ, gp_xInv2, map_add, map_pow, AdjoinRoot.mk_X]
  linear_combination (1 + x) * x128 + (x + x ^ 2 + x ^ 3 + x ^ 7 + x ^ 8) * two_Q

/-! ## Loads and stores -/

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat}
    (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

/-- `rev64 .16b` reverses the bytes of each doubleword. -/
theorem vdword_rev64b (v : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VRevOp.eval .rev64b v) e = rev64 (vdword v e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hr : rev64 (vdword v e) = byteRev64 (vdword v e) := rfl
  rw [hr, getLsbD_byteRev64 _ _ hi]
  simp only [vdword, VRevOp.eval, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * (7 - i / 8) + i % 8 < 64 by omega]
  rw [show 64 * e + i = 8 * (8 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (Nat.mod_lt _ (by decide)), vbyte, BitVec.getLsbD_extractLsb',
    decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  exact congrArg _ (by omega)

theorem rev64b_rev64b (v : BitVec 128) : VRevOp.eval .rev64b (VRevOp.eval .rev64b v) = v := by
  have h : ∀ a : BitVec 64, rev64 (rev64 a) = a := byteRev64_byteRev64
  rw [vdwords (VRevOp.eval .rev64b _), vdword_rev64b _ (by decide), vdword_rev64b _ (by decide),
    vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), h, h, ← vdwords]

end VG.Proof.Gcm.AArch64.Pmull
