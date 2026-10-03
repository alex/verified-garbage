import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# X25519 on AArch64: field elements as fifteen 17-bit limbs

The numbers the code of `Impl/X25519/AArch64.lean` computes, as natural
numbers: the limbs `f 0, …, f 14` stand for `val15 f = Σ f i · 2^(17 i)`, and
each operation is a function of the limbs, computed as the machine does
(modulo `2⁶⁴`); here they are shown to compute the field operations, for limbs
within bounds (`Bnd f k`: every limb is less than `2^k`).
-/

namespace VG.Proof.X25519.AArch64

open VG.Spec.X25519 VG.Proof.X25519

/-- `Σ_{i < n} f i · 2^(17 i)`. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => valN f n + f n * 2 ^ (17 * n)

/-- The number with the limbs `f 0, …, f 14`. -/
abbrev val15 (f : Nat → Nat) : Nat := valN f 15

/-- Every limb is less than `2^k`. -/
def Bnd (f : Nat → Nat) (k : Nat) : Prop := ∀ i < 15, f i < 2 ^ k

theorem Bnd.mono {f : Nat → Nat} {k k' : Nat} (h : Bnd f k) (hk : k ≤ k') : Bnd f k' :=
  fun i hi => Nat.lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by decide) hk)

theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) : valN f n = valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, valN, ih fun i hi => h i (by omega), h n (by omega)]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 17) : valN f n < 2 ^ (17 * n) := by
  induction n with
  | zero => simp [valN]
  | succ n ih =>
    rw [valN]
    have h1 := ih fun i hi => h i (by omega)
    have h2 := h n (by omega)
    have : f n * 2 ^ (17 * n) + 2 ^ (17 * n) ≤ 2 ^ 17 * 2 ^ (17 * n) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h2
    rw [show 17 * (n + 1) = 17 + 17 * n by omega, Nat.pow_add]
    omega

/-! ## Products -/

section
open Fin.CommRing

/-- `2¹⁷` in the field. -/
abbrev X : Fe := 2 ^ 17

theorem X_pow_15 : X ^ 15 = 19 := by decide

theorem toFe_eq_cast (x : Nat) : toFe x = (x : Fe) := rfl

theorem cast_valN (f : Nat → Nat) (n : Nat) :
    ((valN f n : Nat) : Fe) = ∑ i ∈ Finset.range n, (f i : Fe) * X ^ i := by
  induction n with
  | zero => simp [valN]
  | succ n ih => rw [valN, Finset.sum_range_succ, ← ih]; push_cast; rw [pow_mul]

/-- The coefficient of `aᵢ` in column `k`: `b_{k-i}`, or `19 b_{k+15-i}` for a
product that folds. -/
def coef (g : Nat → Nat) (k i : Nat) : Nat := if i ≤ k then g (k - i) else 19 * g (k + 15 - i)

/-- Multiplying by `2^(17 i)` rotates the limbs, folding the top ones back as
19 times them. -/
theorem row (g : Nat → Nat) {i : Nat} (hi : i < 15) :
    X ^ i * ∑ j ∈ Finset.range 15, (g j : Fe) * X ^ j =
      ∑ k ∈ Finset.range 15, (coef g k i : Fe) * X ^ k := by
  induction i with
  | zero => simp [coef]
  | succ i ih =>
    rw [pow_succ, mul_comm (X ^ i) X, mul_assoc, ih (by omega), Finset.mul_sum,
      Finset.sum_range_succ, Finset.sum_range_succ' _ 14]
    have h14 : (coef g 14 i : Fe) = g (14 - i) := by
      simp only [coef, show i ≤ 14 by omega, ite_true]
    have h0 : (coef g 0 (i + 1) : Fe) = 19 * g (14 - i) := by
      simp only [coef, show ¬ i + 1 ≤ 0 by omega, ite_false, show 0 + 15 - (i + 1) = 14 - i by omega]
      push_cast; rfl
    have hk : ∀ k ∈ Finset.range 14, X * ((coef g k i : Fe) * X ^ k) =
        (coef g (k + 1) (i + 1) : Fe) * X ^ (k + 1) := by
      intro k _
      have : coef g (k + 1) (i + 1) = coef g k i := by
        simp only [coef]
        by_cases h : i ≤ k
        · rw [ite_eq_left (by omega : i + 1 ≤ k + 1), ite_eq_left h, show k + 1 - (i + 1) = k - i by omega]
        · rw [ite_eq_right (by omega : ¬ i + 1 ≤ k + 1), ite_eq_right h, show k + 1 + 15 - (i + 1) = k + 15 - i by omega]
      rw [this, pow_succ]; ring
    rw [Finset.sum_congr rfl hk, h14, h0, show X * ((g (14 - i) : Fe) * X ^ 14) = g (14 - i) * X ^ 15 by
      ring, X_pow_15]
    ring

/-- The products of column `k` that do not fold. -/
def lo (f g : Nat → Nat) (k : Nat) : Nat := ∑ i ∈ Finset.range (k + 1), f i * g (k - i)

/-- The products `f (k + 1 + j) · g (14 - j)` that fold into column `k`. -/
def hi (f g : Nat → Nat) (k : Nat) : Nat := ∑ j ∈ Finset.range (14 - k), f (k + 1 + j) * g (14 - j)

theorem column (f g : Nat → Nat) {k : Nat} (hk : k < 15) :
    ∑ i ∈ Finset.range 15, f i * coef g k i = lo f g k + 19 * hi f g k := by
  rw [show 15 = (k + 1) + (14 - k) by omega, Finset.sum_range_add, lo, hi, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [coef, show i ≤ k by simp at hi; omega, ite_true]
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp only [coef, show ¬ k + 1 + j ≤ k by omega, ite_false]
    rw [show k + 15 - (k + 1 + j) = 14 - j by omega]
    ring

/-- The columns of the product of `f` and `g`, folded: a number congruent to
the product. -/
theorem product (f g : Nat → Nat) :
    toFe (valN (fun k => lo f g k + 19 * hi f g k) 15) = toFe (valN f 15) * toFe (valN g 15) := by
  simp only [toFe_eq_cast, cast_valN]
  rw [Finset.sum_mul]
  have e : ∀ i ∈ Finset.range 15, (f i : Fe) * X ^ i * ∑ j ∈ Finset.range 15, (g j : Fe) * X ^ j =
      ∑ k ∈ Finset.range 15, (f i : Fe) * (coef g k i : Fe) * X ^ k := by
    intro i hi
    rw [mul_assoc, row g (by simpa using hi), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_mul, ← column f g (by simpa using hk)]
  push_cast
  rfl

end

/-! ## The product, as the code computes it -/

/-- Column `k` as the code computes it (modulo `2⁶⁴`). -/
def colM (f g : Nat → Nat) (k : Nat) : Nat := (lo f g k % 2 ^ 64 + hi f g k % 2 ^ 64 * 19) % 2 ^ 64

/-- The columns (zero beyond the fifteenth). -/
def cols (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then colM f g k else 0

theorem prod_le {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) {i j : Nat} (hi : i < 15)
    (hj : j < 15) : f i * g j ≤ 2 ^ 52 :=
  Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt (hf i hi)) (Nat.le_of_lt (hg j hj))) (by decide)

theorem sum_le {t : Nat → Nat} {c : Nat} : ∀ n, (∀ i < n, t i ≤ c) →
    ∑ i ∈ Finset.range n, t i ≤ n * c
  | 0, _ => by simp
  | n + 1, h => by
    rw [Finset.sum_range_succ, Nat.succ_mul]
    exact Nat.add_le_add (sum_le n fun i hi => h i (by omega)) (h n (by omega))

theorem lo_le {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) {k : Nat} (hk : k < 15) :
    lo f g k ≤ 15 * 2 ^ 52 :=
  Nat.le_trans (sum_le (k + 1) fun i hi => prod_le hf hg (by omega) (by omega))
    (Nat.mul_le_mul_right _ (by omega))

theorem hi_le {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) {k : Nat} (hk : k < 15) :
    hi f g k ≤ 15 * 2 ^ 52 :=
  Nat.le_trans (sum_le (14 - k) fun j hj => prod_le hf hg (by omega) (by omega))
    (Nat.mul_le_mul_right _ (by omega))

theorem colM_eq {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) {k : Nat} (hk : k < 15) :
    colM f g k = lo f g k + 19 * hi f g k ∧ colM f g k ≤ 2 ^ 61 := by
  have h1 := lo_le hf hg hk
  have h2 := hi_le hf hg hk
  simp only [colM]
  rw [Nat.mod_eq_of_lt (by omega : lo f g k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : hi f g k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem cols_spec {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) :
    (∀ k < 15, cols f g k ≤ 2 ^ 61) ∧ toFe (val15 (cols f g)) = toFe (val15 f) * toFe (val15 g) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [cols, hk, ite_true]; exact (colM_eq hf hg hk).2
  · rw [← product]
    refine congrArg toFe ?_
    exact valN_congr fun k hk => by simp only [cols, hk, ite_true]; exact (colM_eq hf hg hk).1

/-! ## Carries -/

/-- The carry out of limb `k` into limb `k'`, as the code computes it. -/
def cstep (k k' : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if i = k then f k % 2 ^ 17 else if i = k' then (f k' + f k / 2 ^ 17) % 2 ^ 64 else f i

/-- The carries from limb 0 to limb `n`. -/
def chainN (f : Nat → Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => cstep n (n + 1) (chainN f n)

/-- The carry out of limb 14 folded into limb 0, as 19 times it. -/
def cfold (f : Nat → Nat) (i : Nat) : Nat :=
  if i = 14 then f 14 % 2 ^ 17 else if i = 0 then (f 0 + f 14 / 2 ^ 17 * 19) % 2 ^ 64 else f i

/-- The carries of `carry`. -/
def carryF (f : Nat → Nat) : Nat → Nat := cstep 1 2 (cstep 0 1 (cfold (chainN f 14)))

/-- Two limbs that stand for the same number. -/
theorem valN_two {f g : Nat → Nat} {k n : Nat} (hn : k + 2 ≤ n) (hlo : ∀ i < k, g i = f i)
    (hhi : ∀ i, k + 1 < i → g i = f i) (h : g k + 2 ^ 17 * g (k + 1) = f k + 2 ^ 17 * f (k + 1)) :
    valN g n = valN f n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [valN]
    rw [valN_congr hlo, show 17 * (k + 1) = 17 * k + 17 by omega, Nat.pow_add]
    have e : g k * 2 ^ (17 * k) + g (k + 1) * (2 ^ (17 * k) * 2 ^ 17) =
        (g k + 2 ^ 17 * g (k + 1)) * 2 ^ (17 * k) := by
      rw [Nat.add_mul, Nat.mul_comm (2 ^ 17), Nat.mul_assoc, Nat.mul_comm (2 ^ 17)]
    have e' : f k * 2 ^ (17 * k) + f (k + 1) * (2 ^ (17 * k) * 2 ^ 17) =
        (f k + 2 ^ 17 * f (k + 1)) * 2 ^ (17 * k) := by
      rw [Nat.add_mul, Nat.mul_comm (2 ^ 17), Nat.mul_assoc, Nat.mul_comm (2 ^ 17)]
    rw [Nat.add_assoc, e, h, ← e', ← Nat.add_assoc]
  | succ n hn ih => rw [valN, valN, ih, hhi n (by omega)]

theorem cstep_val {f : Nat → Nat} {k : Nat} (hk : k + 2 ≤ 15)
    (h : f (k + 1) + f k / 2 ^ 17 < 2 ^ 64) : valN (cstep k (k + 1) f) 15 = valN f 15 := by
  refine valN_two hk (fun i hi => ?_) (fun i hi => ?_) ?_
  · simp only [cstep, show i ≠ k by omega, show i ≠ k + 1 by omega, ite_false]
  · simp only [cstep, show i ≠ k by omega, show i ≠ k + 1 by omega, ite_false]
  · simp only [cstep, ite_true, show k + 1 ≠ k by omega, ite_false]
    rw [Nat.mod_eq_of_lt h]
    omega

theorem chainN_spec {f : Nat → Nat} {M : Nat} (hM : M + M / 2 ^ 16 < 2 ^ 64)
    (hf : ∀ i < 15, f i ≤ M) {n : Nat} (hn : n ≤ 14) :
    (∀ i < n, chainN f n i < 2 ^ 17) ∧ chainN f n n ≤ M + M / 2 ^ 16 ∧
      (∀ i, n < i → chainN f n i = f i) ∧ valN (chainN f n) 15 = valN f 15 := by
  induction n with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun _ _ => rfl, rfl⟩
    have := hf 0 (by decide)
    exact Nat.le_trans this (Nat.le_add_right _ _)
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    have hn1 : chainN f n (n + 1) = f (n + 1) := h3 (n + 1) (by omega)
    have hf1 := hf (n + 1) (by omega)
    have hc : chainN f n n / 2 ^ 17 ≤ M / 2 ^ 16 := by omega
    have hsum : chainN f n (n + 1) + chainN f n n / 2 ^ 17 < 2 ^ 64 := by omega
    simp only [chainN]
    refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [cstep]
      by_cases hin : i = n
      · rw [ite_eq_left hin]; exact Nat.mod_lt _ (by decide)
      · rw [ite_eq_right hin, ite_eq_right (by omega)]; exact h1 i (by omega)
    · simp only [cstep, show n + 1 ≠ n by omega, ite_false, ite_true]
      rw [Nat.mod_eq_of_lt hsum]; omega
    · simp only [cstep, show i ≠ n by omega, show i ≠ n + 1 by omega, ite_false]
      exact h3 i (by omega)
    · rw [cstep_val (by omega) hsum, h4]

theorem chainN_beyond {f : Nat → Nat} {n i : Nat} (hn : n ≤ 14) (hi : 15 ≤ i) : chainN f n i = f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [chainN, cstep, show i ≠ n by omega, show i ≠ n + 1 by omega, ite_false]
    exact ih (by omega)

/-- Folding the carry out of limb 14, as numbers. -/
theorem cfold_valN {f : Nat → Nat} (h : f 0 + f 14 / 2 ^ 17 * 19 < 2 ^ 64) :
    val15 (cfold f) + 2 ^ 255 * (f 14 / 2 ^ 17) = val15 f + 19 * (f 14 / 2 ^ 17) := by
  have hc : ∀ i, 0 < i → i < 14 → cfold f i = f i := fun i h0 h14 => by
    simp only [cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]
  have h0 : cfold f 0 = f 0 + f 14 / 2 ^ 17 * 19 := by
    simp only [cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt h
  have h14 : cfold f 14 = f 14 % 2 ^ 17 := by simp only [cfold, ite_true]
  simp only [val15, valN, h0, h14, hc 1 (by decide) (by decide), hc 2 (by decide) (by decide),
    hc 3 (by decide) (by decide), hc 4 (by decide) (by decide), hc 5 (by decide) (by decide),
    hc 6 (by decide) (by decide), hc 7 (by decide) (by decide), hc 8 (by decide) (by decide),
    hc 9 (by decide) (by decide), hc 10 (by decide) (by decide), hc 11 (by decide) (by decide),
    hc 12 (by decide) (by decide), hc 13 (by decide) (by decide)]
  omega

/-- Folding the carry out of limb 14 does not change the number modulo `p`. -/
theorem cfold_val {f : Nat → Nat} (h : f 0 + f 14 / 2 ^ 17 * 19 < 2 ^ 64) :
    toFe (val15 (cfold f)) = toFe (val15 f) := by
  have e' := congrArg toFe (cfold_valN h)
  rw [toFe_add rfl, toFe_add rfl,
    toFe_congr (by have := fold255 0 (f 14 / 2 ^ 17); rwa [Nat.zero_add, Nat.zero_add] at this :
      2 ^ 255 * (f 14 / 2 ^ 17) % P = 19 * (f 14 / 2 ^ 17) % P)] at e'
  exact add_right_cancel e'

theorem cfold_beyond {f : Nat → Nat} {i : Nat} (hi : 15 ≤ i) : cfold f i = f i := by
  simp only [cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]

theorem cstep_beyond {f : Nat → Nat} {k k' i : Nat} (hk : k < 15) (hk' : k' < 15) (hi : 15 ≤ i) :
    cstep k k' f i = f i := by
  simp only [cstep, show i ≠ k by omega, show i ≠ k' by omega, ite_false]

/-- The carries of a product: from limbs of at most `2⁶¹`, limbs below `2¹⁸`
standing for the same number modulo `p`. -/
theorem carryF_spec {f : Nat → Nat} (hf : ∀ i < 15, f i ≤ 2 ^ 61) :
    Bnd (carryF f) 18 ∧ toFe (val15 (carryF f)) = toFe (val15 f) ∧ ∀ i, 15 ≤ i → carryF f i = f i := by
  obtain ⟨c1, c2, c3, c4⟩ := chainN_spec (M := 2 ^ 61) (by decide) hf (n := 14) (by decide)
  generalize hg : chainN f 14 = g at c1 c2 c3 c4
  have g0 := c1 0 (by decide)
  have g1 := c1 1 (by decide)
  have g2 := c1 2 (by decide)
  have hfold : g 0 + g 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v1 := cfold_val hfold
  generalize hg1 : cfold g = g1 at v1
  have e0 : g1 0 = g 0 + g 14 / 2 ^ 17 * 19 := by
    rw [← hg1]; simp only [cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]
    exact Nat.mod_eq_of_lt hfold
  have e14 : g1 14 < 2 ^ 17 := by rw [← hg1]; simp only [cfold, ite_true]; exact Nat.mod_lt _ (by decide)
  have eo : ∀ i, 0 < i → i < 14 → g1 i = g i := fun i h0 h14 => by
    rw [← hg1]; simp only [cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]
  have s1 : g1 1 + g1 0 / 2 ^ 17 < 2 ^ 64 := by rw [eo 1 (by decide) (by decide), e0]; omega
  have v2 := cstep_val (f := g1) (k := 0) (by decide) s1
  generalize hg2 : cstep 0 1 g1 = g2 at v2
  have f0 : g2 0 < 2 ^ 17 := by rw [← hg2]; simp only [cstep, ite_true]; exact Nat.mod_lt _ (by decide)
  have f1 : g2 1 = g1 1 + g1 0 / 2 ^ 17 := by
    rw [← hg2]; simp only [cstep, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
    exact Nat.mod_eq_of_lt s1
  have fo : ∀ i, 1 < i → g2 i = g1 i := fun i h => by
    rw [← hg2]; simp only [cstep, show i ≠ 0 by omega, show i ≠ 1 by omega, ite_false]
  have s2 : g2 2 + g2 1 / 2 ^ 17 < 2 ^ 64 := by
    rw [fo 2 (by decide), eo 2 (by decide) (by decide), f1, eo 1 (by decide) (by decide), e0]; omega
  have v3 := cstep_val (f := g2) (k := 1) (by decide) s2
  have hC : carryF f = cstep 1 2 g2 := by rw [carryF, hg, hg1, hg2]
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [hC]; simp only [cstep]
    by_cases h1 : i = 1
    · rw [ite_eq_left h1]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    by_cases h2 : i = 2
    · rw [ite_eq_right h1, ite_eq_left h2, Nat.mod_eq_of_lt s2, fo 2 (by decide),
        eo 2 (by decide) (by decide), f1, eo 1 (by decide) (by decide), e0]
      omega
    rw [ite_eq_right h1, ite_eq_right h2]
    by_cases h0 : i = 0
    · subst h0; exact Nat.lt_trans f0 (by decide)
    rw [fo i (by omega)]
    by_cases h14 : i = 14
    · subst h14; exact Nat.lt_trans e14 (by decide)
    rw [eo i (by omega) (by omega)]
    exact Nat.lt_trans (c1 i (by omega)) (by decide)
  · rw [hC]
    rw [congrArg toFe v3, congrArg toFe v2, v1]
    exact congrArg toFe c4
  · simp only [carryF]
    rw [cstep_beyond (by decide) (by decide) hi, cstep_beyond (by decide) (by decide) hi,
      cfold_beyond hi, chainN_beyond (by decide) hi]

/-- The product, as `mul` computes it. -/
def mulF (f g : Nat → Nat) : Nat → Nat := carryF (cols f g)

theorem mulF_spec {f g : Nat → Nat} (hf : Bnd f 26) (hg : Bnd g 26) :
    Bnd (mulF f g) 18 ∧ toFe (val15 (mulF f g)) = toFe (val15 f) * toFe (val15 g) := by
  obtain ⟨h1, h2⟩ := cols_spec hf hg
  obtain ⟨c1, c2, -⟩ := carryF_spec h1
  exact ⟨c1, c2.trans h2⟩

/-- The limbs times `a24 = 121665`, as `mulSmall` computes them. -/
def scaleF (f : Nat → Nat) (k : Nat) : Nat := if k < 15 then f k * 121665 % 2 ^ 64 else 0

def mulSmallF (f : Nat → Nat) : Nat → Nat := carryF (scaleF f)

theorem valN_mul (c : Nat) (f : Nat → Nat) (n : Nat) : valN (fun i => f i * c) n = c * valN f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [valN, ih, Nat.mul_add]; rw [Nat.mul_comm (f n) c, Nat.mul_assoc]

theorem mulSmallF_spec {f : Nat → Nat} (hf : Bnd f 26) :
    Bnd (mulSmallF f) 18 ∧ toFe (val15 (mulSmallF f)) = a24 * toFe (val15 f) := by
  have hs : ∀ k < 15, scaleF f k = f k * 121665 := fun k hk => by
    simp only [scaleF, hk, ite_true]
    have := hf k hk
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨c1, c2, -⟩ := carryF_spec (f := scaleF f) fun k hk => by rw [hs k hk]; have := hf k hk; omega
  refine ⟨c1, ?_⟩
  rw [mulSmallF, c2, val15, valN_congr hs, valN_mul]
  exact toFe_a24 rfl

/-! ## Sums and differences -/

/-- The sum, as `add` computes it. -/
def addF (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then (f k + g k) % 2 ^ 64 else 0

theorem valN_add (f g : Nat → Nat) (n : Nat) : valN (fun i => f i + g i) n = valN f n + valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [valN, ih, Nat.add_mul]; omega

theorem addF_spec {f g : Nat → Nat} {a b : Nat} (hf : Bnd f a) (hg : Bnd g b) (ha : a ≤ 62)
    (hb : b ≤ a) : Bnd (addF f g) (a + 1) ∧ toFe (val15 (addF f g)) = toFe (val15 f) + toFe (val15 g) := by
  have e : ∀ k < 15, addF f g k = f k + g k := fun k hk => by
    have h1 := hf k hk
    have h2 := hg k hk
    have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hb
    have : 2 ^ a ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) ha
    simp only [addF, hk, ite_true]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨fun k hk => ?_, ?_⟩
  · have h1 := hf k hk
    have h2 := hg k hk
    have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hb
    rw [e k hk, Nat.pow_succ]; omega
  · rw [val15, valN_congr e, valN_add]; exact toFe_add rfl

/-- The limbs of `16 p`. -/
def p16 (i : Nat) : Nat := if i = 0 then 2 ^ 21 - 304 else 2 ^ 21 - 16

theorem valN_p16 : valN p16 15 = 16 * P := by decide

/-- `x + y - z` as `add` then `sub` compute it. -/
def subL (x y z : Nat) : Nat := (2 ^ 64 - z + (x + y) % 2 ^ 64) % 2 ^ 64

/-- The difference, as `sub` computes it: `f + 16 p - g`. -/
def subF (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then subL (f k) (p16 k) (g k) else 0

theorem subF_spec {f g : Nat → Nat} {a : Nat} (hf : Bnd f a) (hg : Bnd g 20) (ha : 21 ≤ a)
    (ha' : a ≤ 62) : Bnd (subF f g) (a + 1) ∧ toFe (val15 (subF f g)) = toFe (val15 f) - toFe (val15 g) := by
  have hp : ∀ k, 2 ^ 21 - 304 ≤ p16 k ∧ p16 k ≤ 2 ^ 21 := fun k => by
    simp only [p16]; split <;> omega
  have e : ∀ k < 15, subF f g k + g k = f k + p16 k := fun k hk => by
    have h1 := hf k hk
    have h2 := hg k hk
    have h3 := hp k
    have : 2 ^ a ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) ha'
    simp only [subF, subL, hk, ite_true]
    rw [Nat.mod_eq_of_lt (by omega : f k + p16 k < 2 ^ 64)]
    omega
  refine ⟨fun k hk => ?_, ?_⟩
  · have h1 := hf k hk
    have h3 := hp k
    have := e k hk
    have : 2 ^ 21 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
    rw [Nat.pow_succ]; omega
  · refine toFe_sub ?_
    have e' : valN (fun k => subF f g k + g k) 15 = valN (fun k => f k + p16 k) 15 := valN_congr e
    rw [valN_add, valN_add, valN_p16] at e'
    rw [e', Nat.mul_comm 16 P, Nat.add_mul_mod_self_left]

end VG.Proof.X25519.AArch64
