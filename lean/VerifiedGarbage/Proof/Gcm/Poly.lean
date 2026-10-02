import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import VerifiedGarbage.Proof.Gcm.Spec
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# GCM: the field GF(2¹²⁸) as polynomials

SP 800-38D §6.3 defines the product of two blocks bit by bit
(`Spec.Gcm.mul`). A block `v` stands for the polynomial `gp v` over GF(2)
whose coefficient of `xⁱ` is bit `i` of `v` from the left (`getMsbD i`), and
`Spec.Gcm.mul` is the product of polynomials modulo
`g = x¹²⁸ + x⁷ + x² + x + 1` (`φ_mul`), in the ring `Q = GF(2)[x] / (g)`,
where `φ v` is the class of `gp v`. Blocks are determined by their classes
(`φ_inj`), so implementations are proven correct by computing in `Q`.
-/

open VG.PowLit

namespace VG.Proof.Gcm.Poly

open Polynomial

abbrev P := Polynomial (ZMod 2)

/-- The polynomial of the bits of `v`: bit `i` from the left (the most
significant first) is the coefficient of `Xⁱ`. -/
noncomputable def gp {n : Nat} (v : BitVec n) : P :=
  ∑ i ∈ Finset.range n, if v.getMsbD i then X ^ i else 0

/-- The element of GF(2) of a bit. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem coeff_gp {n : Nat} (v : BitVec n) (k : Nat) : (gp v).coeff k = bit (v.getMsbD k) := by
  simp only [gp, finsetSum_coeff, bit]
  have : ∀ i, (if v.getMsbD i then (X ^ i : P) else 0).coeff k =
      if k = i then (if v.getMsbD k then 1 else 0) else 0 := by
    intro i; split_ifs <;> simp_all [coeff_X_pow]
  simp only [this, Finset.sum_ite_eq, Finset.mem_range]
  by_cases h : k < n
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, BitVec.getMsbD, decide_false, Bool.false_and, Bool.false_eq_true]

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

theorem bit_inj {a b : Bool} (h : bit a = bit b) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem gp_ext {n : Nat} {a b : BitVec n} (h : gp a = gp b) : a = b := by
  apply BitVec.eq_of_getMsbD_eq
  intro i _
  have := congrArg (coeff · i) h
  simp only [coeff_gp] at this
  exact bit_inj this

theorem gp_xor {n : Nat} (a b : BitVec n) : gp (a ^^^ b) = gp a + gp b := by
  ext k
  simp only [coeff_add, coeff_gp, BitVec.getMsbD_xor, bit_xor]

theorem gp_zero (n : Nat) : gp (0 : BitVec n) = 0 := by
  ext k
  simp only [BitVec.ofNat_eq_ofNat, coeff_gp, bit, BitVec.getMsbD, BitVec.getLsbD_zero, Bool.and_false, Bool.false_eq_true, ↓reduceIte, coeff_zero]

theorem gp_zero' (n : Nat) : gp (0#n) = 0 := gp_zero n

/-- `a ++ b`: the bits of `a` come first. -/
theorem gp_append {n m : Nat} (a : BitVec n) (b : BitVec m) : gp (a ++ b) = gp a + X ^ n * gp b := by
  ext k
  simp only [coeff_add, coeff_gp, coeff_X_pow_mul', BitVec.getMsbD_append]
  by_cases h : k < n
  · have : ¬ n ≤ k := by omega
    simp only [this, ite_false, add_zero]
  · have : n ≤ k := by omega
    simp only [this, ite_true]
    have e : a.getMsbD k = false := by simp only [BitVec.getMsbD, h, decide_false, Bool.false_and]
    rw [e]; simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_add]

theorem degree_gp_lt {n : Nat} (v : BitVec n) : (gp v).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_gp]
  have e : v.getMsbD m = false := by simp only [BitVec.getMsbD, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
  rw [e]; rfl

/-! ## The field -/

/-- The reduction polynomial `x¹²⁸ + x⁷ + x² + x + 1` (§6.3's `R`). -/
@[irreducible] noncomputable def g : P := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

theorem g_eq : g = X ^ 128 + X ^ 7 + X ^ 2 + X + 1 := by unfold g; rfl

theorem degree_g : g.degree = 128 := by rw [g_eq]; compute_degree!

abbrev Q := AdjoinRoot g

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The element of `Q` of a block. -/
noncomputable def φ (v : BitVec 128) : Q := AdjoinRoot.mk g (gp v)

/-- The class of `X`. -/
noncomputable abbrev x : Q := AdjoinRoot.root g

theorem two_Q : (2 : Q) = 0 := by
  have h : (2 : P) = 0 := CharTwo.two_eq_zero
  rw [← map_ofNat (AdjoinRoot.mk g) 2, h, map_zero]

theorem x128 : x ^ 128 = x ^ 7 + x ^ 2 + x + 1 := by
  have h := congrArg (AdjoinRoot.mk g) g_eq
  rw [AdjoinRoot.mk_self] at h
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  linear_combination -h - (x ^ 7 + x ^ 2 + x + 1) * two_Q

theorem φ_xor (a b : BitVec 128) : φ (a ^^^ b) = φ a + φ b := by
  simp only [φ, gp_xor, map_add]

theorem φ_zero : φ 0 = 0 := by
  simp only [φ, gp_zero, map_zero]

theorem φ_zero' : φ 0#128 = 0 := φ_zero

theorem φ_inj {a b : BitVec 128} (h : φ a = φ b) : a = b := by
  have h' : g ∣ gp (a ^^^ b) := by
    rw [φ, φ, AdjoinRoot.mk_eq_mk] at h
    rwa [gp_xor, ← CharTwo.sub_eq_add]
  have := eq_zero_of_dvd_of_degree_lt h' (by rw [degree_g]; exact degree_gp_lt _)
  rw [← gp_zero 128] at this
  have := congrArg (· ^^^ b) (gp_ext this)
  simpa [BitVec.xor_assoc] using this

/-- `φ v` as the sum of the powers of `x` of its bits. -/
theorem φ_eq (v : BitVec 128) :
    φ v = ∑ i ∈ Finset.range 128, if v.getMsbD i then x ^ i else 0 := by
  simp only [φ, gp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-! ## `Spec.Gcm.mul` is the product in `Q` -/

theorem gp_R : gp Spec.Gcm.R = X ^ 7 + X ^ 2 + X + 1 := by
  have hb : ∀ d < 128, Spec.Gcm.R.getMsbD d = (d = 0 || d = 1 || d = 2 || d = 7) := by decide +kernel
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 7 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 7)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h2, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp only [bit, h0, decide_false, h1, Bool.or_self, h2, h7, Bool.false_eq_true, ↓reduceIte, add_zero, show (1 : Nat) ≠ d from fun h => h1 h.symm]
  · have e : Spec.Gcm.R.getMsbD d = false := by simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
    rw [e]
    simp only [show d ≠ 7 by omega, show d ≠ 2 by omega, show 1 ≠ d by omega, show d ≠ 0 by omega,
      ite_false]
    rfl

theorem gp_shr1 (v : BitVec 128) :
    gp (v >>> 1) + (if v.getLsbD 0 then X ^ 128 else 0) = X * gp v := by
  ext d
  simp only [coeff_add, coeff_gp]
  rcases d with _ | d
  · simp only [coeff_X_mul_zero]
    have e : (v >>> 1).getMsbD 0 = false := by simp only [BitVec.getMsbD_ushiftRight, Nat.ofNat_pos, decide_true, Order.lt_one_iff, Bool.not_true, zero_tsub, Bool.false_and, Bool.and_false]
    rw [e]; split_ifs <;> simp [bit, coeff_X_pow]
  · rw [coeff_X_mul, coeff_gp]
    by_cases hd : d = 127
    · subst hd
      have e : (v >>> 1).getMsbD 128 = false := by simp only [BitVec.getMsbD, lt_self_iff_false, decide_false, Nat.add_one_sub_one, Nat.reduceLeDiff, Nat.sub_eq_zero_of_le, Nat.ofNat_pos, BitVec.getLsbD_eq_getElem, BitVec.getElem_ushiftRight, add_zero, Nat.one_lt_ofNat, Bool.false_and]
      rw [e]
      have e' : v.getMsbD 127 = v.getLsbD 0 := by simp only [BitVec.getMsbD, Nat.lt_add_one, decide_true, Nat.add_one_sub_one, tsub_self, Nat.ofNat_pos, BitVec.getLsbD_eq_getElem, Bool.true_and]
      rw [e']
      cases v.getLsbD 0 <;> simp [bit, coeff_X_pow]
    · have e : (v >>> 1).getMsbD (d + 1) = v.getMsbD d := by
        simp only [BitVec.getMsbD, BitVec.getLsbD_ushiftRight]
        by_cases h : d < 128
        · simp only [show d + 1 < 128 by omega, h, decide_true, Bool.true_and]
          congr 1; omega
        · simp only [show ¬ d + 1 < 128 by omega, h, decide_false, Bool.false_and]
      rw [e]
      split_ifs <;> simp [coeff_X_pow, hd]

theorem φ_shr1 (v : BitVec 128) :
    φ (if v.getLsbD 0 then (v >>> 1) ^^^ Spec.Gcm.R else v >>> 1) = x * φ v := by
  have h := congrArg (AdjoinRoot.mk g) (gp_shr1 v)
  simp only [map_add, map_mul, AdjoinRoot.mk_X] at h
  change _ = AdjoinRoot.root g * AdjoinRoot.mk g (gp v)
  rw [← h]
  split_ifs with hv
  · rw [φ_xor]
    simp only [φ, gp_R, map_add, map_pow, map_one, AdjoinRoot.mk_X, x128]
  · simp only [φ, map_zero, add_zero]

theorem mulSteps_φ (a b : Spec.Gcm.Block) (k : Nat) :
    φ (mulSteps a b k).2 = φ b * x ^ k ∧
      φ (mulSteps a b k).1 = φ b * ∑ i ∈ Finset.range k, (if a.getMsbD i then x ^ i else 0) := by
  induction k with
  | zero => exact ⟨by simp only [mulSteps_zero, BitVec.ofNat_eq_ofNat, pow_zero, mul_one], by simpa [mulSteps_zero] using φ_zero⟩
  | succ k ih =>
    rw [mulSteps_succ]
    simp only [mulStep, φ_shr1, Finset.sum_range_succ]
    refine ⟨by rw [ih.1]; ring, ?_⟩
    split_ifs
    · rw [φ_xor, ih.1, ih.2]; ring
    · rw [ih.2]; ring

/-- §6.3's product is the product in `Q`. -/
theorem φ_mul (a b : Spec.Gcm.Block) : φ (Spec.Gcm.mul a b) = φ a * φ b := by
  rw [mul_eq, (mulSteps_φ a b 128).2, φ_eq a, mul_comm]

end VG.Proof.Gcm.Poly
