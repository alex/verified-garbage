import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs

/-!
# GHASH with PCLMULQDQ: the arithmetic

Untrusted: everything here is checked by Lean. What the instructions of
`Impl.Gcm.X86_64.Pclmul` compute, in the ring `Q` of `Proof/Gcm/Poly.lean`:

* `pclmulqdq` multiplies polynomials (`gp_clmul`), so the four of `acc`
  compute `x · a · b` as a 256-bit value (`Prod.val_prod`);
* `reduce` maps a 256-bit value to a block of the same class
  (`φ_reduce`);
* `hInv` computes `H · x⁻¹` (`x_φ_hInv`).
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open Polynomial
open VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (poly xInv)

/-! ## Carry-less multiplication -/

theorem gp_shl (b : BitVec 64) {j : Nat} (hj : j < 64) :
    gp ((b.setWidth 128) <<< j) = X ^ (64 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 64 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 128 - 64 ≤ d + j by omega), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [h, ite_false, decide_eq_false (show ¬ 128 - 64 ≤ d + j by omega), Bool.false_and]; rfl

/-- The first `k` steps of `clmul`. -/
def clSteps (a b : BitVec 64) (k : Nat) : BitVec 128 :=
  (List.range k).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

theorem gp_clSteps (a b : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    gp (clSteps a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (63 - i) else 0) * gp b := by
  induction k with
  | zero => simp [clSteps, gp_zero']
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

/-- `pclmulqdq` multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_clmul (a b : BitVec 64) : gp (clmul a b) = X * gp a * gp b := by
  rw [show clmul a b = clSteps a b 64 from rfl, gp_clSteps a b (Nat.le_refl _), gp_lsb]

/-! ## Quadwords -/

theorem qwords (v : BitVec 128) : v = qword v 1 ++ qword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp [h]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem gp_qwords (v : BitVec 128) : gp v = gp (qword v 1) + X ^ 64 * gp (qword v 0) := by
  conv => lhs; rw [qwords v]
  rw [gp_append]

theorem φ_qwords (v : BitVec 128) :
    φ v = AdjoinRoot.mk g (gp (qword v 1)) + x ^ 64 * AdjoinRoot.mk g (gp (qword v 0)) := by
  rw [φ, gp_qwords]; simp

/-- The class of a 64-bit polynomial. -/
noncomputable def ψ (q : BitVec 64) : Q := AdjoinRoot.mk g (gp q)

theorem φ_clmul (a b : BitVec 64) : φ (clmul a b) = x * ψ a * ψ b := by
  simp only [φ, ψ, gp_clmul, map_mul, AdjoinRoot.mk_X]

theorem φ_q (v : BitVec 128) : φ v = ψ (qword v 1) + x ^ 64 * ψ (qword v 0) := φ_qwords v

/-! ## The product of two blocks, as 256 bits -/

/-- A 256-bit carry-less product, as its `lo`, `mid` and `hi` parts. -/
structure Prod where
  lo : BitVec 128
  mid : BitVec 128
  hi : BitVec 128

namespace Prod

/-- Its class: `hi` holds the low powers. -/
noncomputable def val (p : Prod) : Q := φ p.hi + x ^ 64 * φ p.mid + x ^ 128 * φ p.lo

def xor (p q : Prod) : Prod := ⟨p.lo ^^^ q.lo, p.mid ^^^ q.mid, p.hi ^^^ q.hi⟩

/-- The four products of `acc`, added to `p`. -/
def acc (p : Prod) (a b : BitVec 128) : Prod :=
  ⟨p.lo ^^^ pclmul a b 0x00,
   p.mid ^^^ pclmul a b 0x01 ^^^ pclmul a b 0x10,
   p.hi ^^^ pclmul a b 0x11⟩

def zero : Prod := ⟨0, 0, 0⟩

theorem val_zero : zero.val = 0 := by simp [val, zero, φ_zero']

theorem val_acc (p : Prod) (a b : BitVec 128) : (p.acc a b).val = p.val + x * φ a * φ b := by
  simp only [acc, val, φ_xor]
  simp only [pclmul, show (0x00 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x00 : BitVec 8).getLsbD 4 = false from rfl, show (0x01 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x01 : BitVec 8).getLsbD 4 = false from rfl, show (0x10 : BitVec 8).getLsbD 0 = false from rfl,
    show (0x10 : BitVec 8).getLsbD 4 = true from rfl, show (0x11 : BitVec 8).getLsbD 0 = true from rfl,
    show (0x11 : BitVec 8).getLsbD 4 = true from rfl, ite_true, Bool.false_eq_true, ite_false,
    φ_clmul, φ_q a, φ_q b]
  ring

end Prod

/-! ## The reduction -/

theorem shr64 (v : BitVec 128) : v >>> 64 = 0#64 ++ qword v 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · simp only [h, ite_false, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem shl64 (v : BitVec 128) : v <<< 64 = qword v 0 ++ 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
  by_cases h : i < 64
  · simp [h]
  · simp only [h, ite_false, decide_false, Bool.not_false, Bool.true_and, Nat.mul_zero, Nat.zero_add,
      decide_eq_true (show i - 64 < 64 by omega), decide_eq_true hi, Bool.and_true]

theorem φ_shr64 (v : BitVec 128) : φ (v >>> 64) = x ^ 64 * ψ (qword v 1) := by
  rw [φ, shr64, gp_append, gp_zero']; simp [ψ]

theorem φ_shl64 (v : BitVec 128) : φ (v <<< 64) = ψ (qword v 0) := by
  rw [φ, shl64, gp_append, gp_zero']; simp [ψ]

theorem ψ_c : ψ (qword poly 1) = 1 + x + x ^ 6 := by
  have hb : ∀ d < 64, (qword poly 1).getMsbD d = (d = 0 || d = 1 || d = 6) := by decide
  have h : gp (qword poly 1) = 1 + X + X ^ 6 := by
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
      · simp [bit, h0, h1, h6, show (1 : Nat) ≠ d from fun h => h1 h.symm]
    · have e : (qword poly 1).getMsbD d = false := by simp [BitVec.getMsbD]; omega
      rw [e]
      simp [bit, show d ≠ 6 by omega, show (1 : Nat) ≠ d by omega, show d ≠ 0 by omega]
  simp [ψ, h]

theorem shufDwords_4e (a : BitVec 128) : shufDwords a 0x4e = qword a 0 ++ qword a 1 := by
  rw [show shufDwords a 0x4e = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_ofDwords, getLsbD_dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega)

/-- One step of the reduction: `swap(v) ⊕ clmul(v₀, c)`. -/
def fold (v : BitVec 128) : BitVec 128 := shufDwords v 0x4e ^^^ pclmul v poly 0x10

theorem φ_fold (v : BitVec 128) : φ (fold v) = x ^ 64 * φ v := by
  have e1 : φ (shufDwords v 0x4e) = ψ (qword v 0) + x ^ 64 * ψ (qword v 1) := by
    rw [shufDwords_4e, φ, gp_append]; simp [ψ]
  have e2 : pclmul v poly 0x10 = clmul (qword v 0) (qword poly 1) := rfl
  rw [fold, φ_xor, e1, e2, φ_clmul, ψ_c, φ_q v]
  linear_combination (-ψ (qword v 0)) * x128

/-- The block `reduce` computes from a product. -/
def reduce (p : Prod) : BitVec 128 :=
  (p.hi ^^^ p.mid >>> 64) ^^^ fold (fold (p.lo ^^^ p.mid <<< 64))

theorem φ_reduce (p : Prod) : φ (reduce p) = p.val := by
  simp only [reduce, φ_xor, φ_fold, φ_shr64, φ_shl64, Prod.val, φ_q p.mid]
  ring

/-! ## `H · x⁻¹` -/

theorem shl1 (h : BitVec 128) :
    XShiftOp.eval .psllq h 1 ||| XShiftOp.eval .pslldq (XShiftOp.eval .psrlq h 63) 8 = h <<< 1 := by
  have e1 : XShiftOp.eval .psllq h 1 = (qword h 1 <<< 1) ++ (qword h 0 <<< 1) := rfl
  have e2 : XShiftOp.eval .psrlq h 63 = (qword h 1 >>> 63) ++ (qword h 0 >>> 63) := rfl
  have e3 : ∀ y, XShiftOp.eval .pslldq y 8 = y <<< 64 := fun _ => rfl
  rw [e1, e2, e3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, qword, BitVec.getLsbD_extractLsb']
  rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i < 64) ∨ i = 64 ∨ 64 < i) with h | h | h | h
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true, Bool.not_true]
    exact congrArg _ (by omega)
  · subst h; simp
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.not_false, Bool.false_and, Bool.or_false, Bool.and_false, Bool.and_true,
      Bool.not_true]
    exact congrArg _ (by omega)

theorem shr31 (y : BitVec 32) : y >>> 31 = if y.msb then 1#32 else 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
  have := y.isLt
  split_ifs with h
  · simp at h; simp [Nat.shiftRight_eq_div_pow]; omega
  · simp at h; simp [Nat.shiftRight_eq_div_pow]; omega

theorem msb_dword3 (h : BitVec 128) : dword h 3 >>> 31 = if h.getMsbD 0 then 1#32 else 0#32 := by
  have e : (dword h 3).msb = h.getMsbD 0 := by
    simp only [BitVec.msb_eq_getLsbD_last, getLsbD_dword, BitVec.getMsbD]; rfl
  rw [shr31, e]

/-- The mask of `hInv`: `x⁻¹` if the bit shifted out of `h` is 1, else 0. -/
theorem mask_eq (h : BitVec 128) :
    XBinOp.eval .pandn (XBinOp.eval .paddd (XShiftOp.eval .psrld (shufDwords h 0xff) 31)
      (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
        ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)))) xInv =
      if h.getMsbD 0 then xInv else 0 := by
  have e0 : shufDwords h 0xff = ofDwords (dword h 3) (dword h 3) (dword h 3) (dword h 3) := rfl
  have e1 : ∀ a, XShiftOp.eval .psrld a 31 =
      ofDwords (dword a 0 >>> 31) (dword a 1 >>> 31) (dword a 2 >>> 31) (dword a 3 >>> 31) :=
    fun _ => rfl
  have e2 : XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
      ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) = ofDwords (-1) (-1) (-1) (-1) := by rfl
  rw [e0, e1, e2]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, msb_dword3]
  split_ifs
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (1#32 : BitVec 32) + -1 = 0 by rfl, show ofDwords 0 0 0 0 = 0 by rfl]
    rfl
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      show (0#32 : BitVec 32) + -1 = -1 by rfl,
      show ~~~ofDwords (-1) (-1) (-1) (-1) = 0 by rfl]
    rfl

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
  · have e : xInv.getMsbD d = false := by simp [BitVec.getMsbD]; omega
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

/-- `hInv`'s result is `H · x⁻¹`. -/
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

end VG.Proof.Gcm.X86_64.Pclmul
