import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Reverse
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Impl.Gcm.X86_64
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

section

/-!
# Carry-less products from integer products with holes

Untrusted: everything here is checked by Lean. The arithmetic of
`Impl.Gcm.X86_64.product` (BearSSL's ctmul64): the integer product of two
words whose bits are 4 apart, one of them with at most 8 bits, has the bits
of their carry-less product at the positions of its class (`testBit_ip`),
since the column sums (at most 8) never carry into the next position of the
class. So the classes of the eight parts of `a` and the four of `b`, masked
and added, give the carry-less product of `a` and `b` (`lp_prodVal`), which
in SP 800-38D's reflected bit order is `x · a · b` (`gp_prodVal`).

`lp v` is the polynomial of the bits of `v` with bit `i` from the right the
coefficient of `Xⁱ` (integers' order), and `sp v e m` the polynomial over
`ℕ` of the bits `e + 4u` (`u < m`) of `v`, so that a word whose bits are
only those is `2ᵉ · (sp v e m)(16)`.
-/

open VG.PowLit

namespace VG.Proof.Gcm.X86_64.Ctmul

open Polynomial VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64 (cls half)

/-! ## Polynomials of words, in integers' bit order -/

/-- Bit `i` from the right is the coefficient of `Xⁱ`. -/
noncomputable def lp {n : Nat} (v : BitVec n) : P :=
  ∑ i ∈ Finset.range n, if v.getLsbD i then X ^ i else 0

theorem coeff_lp {n : Nat} (v : BitVec n) (k : Nat) : (lp v).coeff k = bit (v.getLsbD k) := by
  simp only [lp, finsetSum_coeff, bit]
  have : ∀ i, (if v.getLsbD i then (X ^ i : P) else 0).coeff k =
      if k = i then (if v.getLsbD k then 1 else 0) else 0 := by
    intro i; split_ifs <;> simp_all [coeff_X_pow]
  simp only [this, Finset.sum_ite_eq, Finset.mem_range]
  by_cases h : k < n
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge v k (by omega)]

theorem lp_xor {n : Nat} (a b : BitVec n) : lp (a ^^^ b) = lp a + lp b := by
  ext k
  simp only [coeff_add, coeff_lp, BitVec.getLsbD_xor, bit_xor]

theorem lp_ext {n : Nat} {a b : BitVec n} (h : ∀ k, (lp a).coeff k = (lp b).coeff k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have := h i
  simp only [coeff_lp] at this
  exact bit_inj this

theorem natDegree_lp {n : Nat} (v : BitVec n) : (lp v).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_lp, BitVec.getLsbD_of_ge v N (by omega)]
  rfl

/-- `gp` is `lp` read backwards. -/
theorem gp_eq_reflect {n : Nat} (hn : 0 < n) (v : BitVec n) : gp v = reflect (n - 1) (lp v) := by
  ext k
  rw [coeff_reflect, coeff_gp]
  by_cases hk : k ≤ n - 1
  · rw [revAt_le hk, coeff_lp, BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega), Bool.true_and]
  · rw [revAt_eq_self_of_lt (by omega), coeff_lp, BitVec.getLsbD_of_ge v k (by omega)]
    simp [BitVec.getMsbD, show ¬ k < n by omega]

/-- A 128-bit word whose `lp` is the product of two words' is their product
in the reflected order, with a factor `X`. -/
theorem gp_of_lp {r : BitVec 128} {a b : BitVec 64} (h : lp r = lp a * lp b) :
    gp r = X * gp a * gp b := by
  rw [gp_eq_reflect (by omega), gp_eq_reflect (by omega), gp_eq_reflect (by omega), h,
    show (128 - 1 : Nat) = 1 + (63 + 63) by rfl, ← one_mul (lp a * lp b),
    reflect_mul _ _ (natDegree_one.le.trans (Nat.zero_le 1))
      ((natDegree_mul_le).trans (Nat.add_le_add (natDegree_lp a) (natDegree_lp b))),
    reflect_mul _ _ (natDegree_lp a) (natDegree_lp b)]
  simp [mul_assoc]

/-! ## Integers as base-16 digits -/

/-- The digits of `F(16)` are the coefficients of `F`, if they are digits. -/
theorem eval_digit (F : ℕ[X]) (hF : ∀ w, F.coeff w < 16) (w : Nat) :
    F.eval 16 / 16 ^ w % 16 = F.coeff w := by
  induction w generalizing F with
  | zero =>
    have e := congrArg (eval 16) (divX_mul_X_add F)
    simp only [eval_add, eval_mul, eval_X, eval_C] at e
    have := hF 0
    rw [pow_zero, Nat.div_one, ← e]
    omega
  | succ w ih =>
    have e := congrArg (eval 16) (divX_mul_X_add F)
    simp only [eval_add, eval_mul, eval_X, eval_C] at e
    have := hF 0
    have h16 : F.eval 16 / 16 = (divX F).eval 16 := by rw [← e]; omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, h16, ih _ fun w => by rw [coeff_divX]; exact hF _,
      coeff_divX]

theorem testBit_eval (F : ℕ[X]) (hF : ∀ w, F.coeff w < 16) (e w s : Nat) (hs : s < 4) :
    (2 ^ e * F.eval 16).testBit (e + 4 * w + s) = (F.coeff w).testBit s := by
  rw [Nat.testBit_two_pow_mul, decide_eq_true (by omega), Bool.true_and,
    show e + 4 * w + s - e = s + 4 * w by omega, ← Nat.testBit_div_two_pow, pow_mul,
    show (2 : Nat) ^ 4 = 16 by rfl, ← eval_digit F hF w, show (16 : Nat) = 2 ^ 4 by rfl,
    Nat.testBit_mod_two_pow, decide_eq_true hs, Bool.true_and]

theorem testBit_eval_lt (F : ℕ[X]) {e p : Nat} (hp : p < e) : (2 ^ e * F.eval 16).testBit p = false := by
  rw [Nat.testBit_two_pow_mul, decide_eq_false (by omega), Bool.false_and]

/-! ## Words with holes -/

/-- The bits `e + 4u` (`u < m`) of `v`. -/
noncomputable def sp (v : BitVec 64) (e m : Nat) : ℕ[X] :=
  ∑ u ∈ Finset.range m, if v.getLsbD (e + 4 * u) then X ^ u else 0

theorem coeff_sp (v : BitVec 64) (e m u : Nat) :
    (sp v e m).coeff u = if u < m ∧ v.getLsbD (e + 4 * u) then 1 else 0 := by
  simp only [sp, finsetSum_coeff]
  have : ∀ i, (if v.getLsbD (e + 4 * i) then (X ^ i : ℕ[X]) else 0).coeff u =
      if u = i then (if v.getLsbD (e + 4 * u) then 1 else 0) else 0 := by
    intro i; split_ifs <;> simp_all [coeff_X_pow]
  simp only [this, Finset.sum_ite_eq, Finset.mem_range]
  by_cases h : u < m <;> simp [h]

theorem coeff_sp_le (v : BitVec 64) (e m u : Nat) : (sp v e m).coeff u ≤ 1 := by
  rw [coeff_sp]; split_ifs <;> omega

/-- The bits of `v` are among `e + 4u`, `u < m`. -/
def Sparse (v : BitVec 64) (e m : Nat) : Prop :=
  ∀ p, v.getLsbD p = true → e ≤ p ∧ (p - e) % 4 = 0 ∧ p < e + 4 * m

theorem toNat_sparse {v : BitVec 64} {e m : Nat} (h : Sparse v e m) :
    v.toNat = 2 ^ e * (sp v e m).eval 16 := by
  have hF : ∀ w, (sp v e m).coeff w < 16 := fun w => by have := coeff_sp_le v e m w; omega
  apply Nat.eq_of_testBit_eq
  intro p
  rw [BitVec.testBit_toNat]
  by_cases hp : p < e
  · rw [testBit_eval_lt _ hp]
    cases hv : v.getLsbD p
    · rfl
    · have := h p hv; omega
  · obtain ⟨w, s, hs, rfl⟩ : ∃ w s, s < 4 ∧ p = e + 4 * w + s :=
      ⟨(p - e) / 4, (p - e) % 4, Nat.mod_lt _ (by omega), by omega⟩
    rw [testBit_eval _ hF _ _ _ hs, coeff_sp]
    by_cases hs0 : s = 0
    · subst hs0
      rw [Nat.add_zero]
      by_cases hw : w < m
      · cases hv : v.getLsbD (e + 4 * w) <;> simp [hw]
      · cases hv : v.getLsbD (e + 4 * w)
        · simp
        · have := h _ hv; omega
    · have e0 : v.getLsbD (e + 4 * w + s) = false := by
        cases hv : v.getLsbD (e + 4 * w + s)
        · rfl
        · have := h _ hv; omega
      rw [e0]
      split_ifs
      · rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hs0)]
      · simp


/-- A word with holes, over `GF(2)`. -/
theorem lp_sparse {v : BitVec 64} {e m : Nat} (h : Sparse v e m) :
    lp v = X ^ e * expand (ZMod 2) 4 ((sp v e m).map (Nat.castRingHom (ZMod 2))) := by
  ext k
  rw [coeff_lp, coeff_X_pow_mul', coeff_expand (by omega), coeff_map, coeff_sp]
  cases hv : v.getLsbD k
  · split_ifs with h1 h2 h3
    · rw [show e + 4 * ((k - e) / 4) = k by omega, hv] at h3
      simp at h3
    all_goals simp [bit]
  · obtain ⟨h1, h2, h3⟩ := h k hv
    rw [ite_eq_left h1, ite_eq_left (Nat.dvd_of_mod_eq_zero h2), ite_eq_left ⟨by omega,
      by rw [show e + 4 * ((k - e) / 4) = k by omega]; exact hv⟩]
    simp [bit]

/-- Sums of at most `m` bits. -/
theorem sum_range_ite_le (f : Nat → Nat) (hf : ∀ k, f k ≤ 1) (m : Nat) (hm : ∀ k, m ≤ k → f k = 0) :
    ∀ n, ∑ k ∈ Finset.range n, f k ≤ m := by
  have : ∀ n, ∑ k ∈ Finset.range n, f k ≤ min n m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : m ≤ n
      · rw [hm n h]; omega
      · have := hf n; omega
  exact fun n => (this n).trans (Nat.min_le_right _ _)

/-- The column sums of the product of two words with holes, one of them with
at most `m` bits. -/
theorem coeff_sp_mul_le (a b : BitVec 64) (ea eb m mb w : Nat) :
    (sp a ea m * sp b eb mb).coeff w ≤ m := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (Finset.sum_le_sum fun k _ => ?_).trans
    (sum_range_ite_le (fun k => (sp a ea m).coeff k) (coeff_sp_le a ea m) m
      (fun k hk => by rw [coeff_sp, ite_eq_right (by omega)]) _)
  have := coeff_sp_le b eb mb (w - k)
  exact (Nat.mul_le_mul_left _ this).trans (by rw [Nat.mul_one])

theorem bit_testBit_zero (c : Nat) : bit (c.testBit 0) = (c : ZMod 2) := by
  rw [Nat.testBit_zero, ← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h, bit]

/-- What `mul` leaves in `rdx:rax`. -/
def ip (a b : BitVec 64) : BitVec 128 := BitVec.ofNat 128 (a.toNat * b.toNat)

/-- At the positions of their class, the bits of the integer product of two
words with holes, one of them with at most 15 bits, are those of their
carry-less product. -/
theorem bit_ip {a b : BitVec 64} {ea ma eb mb : Nat} (ha : Sparse a ea ma) (hb : Sparse b eb mb)
    (hm : ma < 16) {p : Nat} (hp : p < 128) (hpc : p % 4 = (ea + eb) % 4) :
    bit ((ip a b).getLsbD p) = (lp a * lp b).coeff p := by
  have hF : ∀ w, (sp a ea ma * sp b eb mb).coeff w < 16 :=
    fun w => Nat.lt_of_le_of_lt (coeff_sp_mul_le a b ea eb ma mb w) hm
  have hn : a.toNat * b.toNat = 2 ^ (ea + eb) * (sp a ea ma * sp b eb mb).eval 16 := by
    rw [toNat_sparse ha, toNat_sparse hb, eval_mul, pow_add]; ring
  have hl : lp a * lp b = X ^ (ea + eb) *
      expand (ZMod 2) 4 ((sp a ea ma * sp b eb mb).map (Nat.castRingHom (ZMod 2))) := by
    rw [lp_sparse ha, lp_sparse hb, Polynomial.map_mul, map_mul, pow_add]; ring
  rw [ip, BitVec.getLsbD_ofNat, decide_eq_true hp, Bool.true_and, hn, hl, coeff_X_pow_mul']
  by_cases hlt : p < ea + eb
  · rw [testBit_eval_lt _ hlt, ite_eq_right (by omega)]; rfl
  · obtain ⟨w, rfl⟩ : ∃ w, p = ea + eb + 4 * w := ⟨(p - (ea + eb)) / 4, by omega⟩
    rw [show ea + eb + 4 * w = ea + eb + 4 * w + 0 by rfl, testBit_eval _ hF _ _ _ (by omega),
      ite_eq_left (by omega), show ea + eb + 4 * w + 0 - (ea + eb) = 4 * w by omega,
      coeff_expand (by omega), ite_eq_left (Dvd.intro w rfl), Nat.mul_div_cancel_left _ (by omega),
      coeff_map, bit_testBit_zero]
    rfl

/-- … and the carry-less product has no bits at the other positions. -/
theorem coeff_lp_mul_sparse {a b : BitVec 64} {ea ma eb mb : Nat} (ha : Sparse a ea ma)
    (hb : Sparse b eb mb) {p : Nat} (hpc : p % 4 ≠ (ea + eb) % 4) : (lp a * lp b).coeff p = 0 := by
  rw [lp_sparse ha, lp_sparse hb,
    show ∀ f g : P, X ^ ea * f * (X ^ eb * g) = X ^ (ea + eb) * (f * g) by intros; ring,
    coeff_X_pow_mul', ← map_mul, coeff_expand (by omega)]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl


/-! ## The masks -/

theorem getLsbD_half_lt : ∀ p < 64, ∀ i < 4, ∀ h < 2,
    (half i h).getLsbD p = decide (p % 4 = i ∧ p / 32 = h) := by decide +kernel

theorem getLsbD_cls_lt : ∀ p < 64, ∀ j < 4, (cls j).getLsbD p = decide (p % 4 = j) := by decide +kernel

theorem getLsbD_half {i h : Nat} (hi : i < 4) (hh : h < 2) (p : Nat) :
    (half i h).getLsbD p = decide (p < 64 ∧ p % 4 = i ∧ p / 32 = h) := by
  by_cases hp : p < 64
  · rw [getLsbD_half_lt p hp i hi h hh]; simp [hp]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hp]

theorem getLsbD_cls {j : Nat} (hj : j < 4) (p : Nat) :
    (cls j).getLsbD p = decide (p < 64 ∧ p % 4 = j) := by
  by_cases hp : p < 64
  · rw [getLsbD_cls_lt p hp j hj]; simp [hp]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp [hp]

/-- Part `t` of the first factor. -/
def part (hv : BitVec 64) (t : Nat) : BitVec 64 := hv &&& half (t / 2) (t % 2)

/-- The class of the second factor that part `t` meets in class `k`. -/
def jOf (k t : Nat) : Nat := (k + 4 - t / 2) % 4

theorem sparse_part (hv : BitVec 64) {t : Nat} (ht : t < 8) : Sparse (part hv t) (t / 2 + 32 * (t % 2)) 8 := by
  intro p hp
  rw [part, BitVec.getLsbD_and, getLsbD_half (by omega) (by omega)] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

theorem sparse_cls (yv : BitVec 64) {j : Nat} (hj : j < 4) : Sparse (yv &&& cls j) j 16 := by
  intro p hp
  rw [BitVec.getLsbD_and, getLsbD_cls hj] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

/-! ## The product -/

/-- The first `n` products of class `k`, added. -/
def classSum (hv yv : BitVec 64) (k n : Nat) : BitVec 128 :=
  (List.range n).foldl (fun acc t => acc ^^^ ip (part hv t) (yv &&& cls (jOf k t))) 0

/-- The carry-less product that `product` computes: the classes, masked and added. -/
def prodVal (hv yv : BitVec 64) : BitVec 128 :=
  (List.range 4).foldl (fun r k => r ^^^ (classSum hv yv k 8 &&& (cls k ++ cls k))) 0

theorem classSum_succ (hv yv : BitVec 64) (k n : Nat) :
    classSum hv yv k (n + 1) = classSum hv yv k n ^^^ ip (part hv n) (yv &&& cls (jOf k n)) := by
  simp only [classSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bit_classSum (hv yv : BitVec 64) (k : Nat) (hk : k < 4) {p : Nat} (hp : p < 128)
    (hpk : p % 4 = k) : ∀ n ≤ 8, bit ((classSum hv yv k n).getLsbD p) =
      ∑ t ∈ Finset.range n, (lp (part hv t) * lp (yv &&& cls (jOf k t))).coeff p := by
  intro n hn
  induction n with
  | zero => simp [classSum, bit]
  | succ n ih =>
    rw [classSum_succ, BitVec.getLsbD_xor, bit_xor, ih (by omega), Finset.sum_range_succ,
      bit_ip (sparse_part hv (by omega)) (sparse_cls yv (by simp only [jOf]; omega)) (by omega) hp
        (by simp only [jOf]; omega)]

theorem getLsbD_mask {k : Nat} (hk : k < 4) (p : Nat) :
    (cls k ++ cls k).getLsbD p = decide (p < 128 ∧ p % 4 = k) := by
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · rw [getLsbD_cls hk]; simp only [h, true_and, decide_eq_decide]; omega
  · rw [getLsbD_cls hk]; simp only [decide_eq_decide]; omega

theorem getLsbD_prodVal (hv yv : BitVec 64) {p : Nat} (hp : p < 128) :
    (prodVal hv yv).getLsbD p = (classSum hv yv (p % 4) 8).getLsbD p := by
  simp only [prodVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_mask (show 0 < 4 by omega), getLsbD_mask (show 1 < 4 by omega),
    getLsbD_mask (show 2 < 4 by omega), getLsbD_mask (show 3 < 4 by omega)]
  have : p % 4 < 4 := Nat.mod_lt _ (by omega)
  rcases (by omega : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3) with h | h | h | h <;>
    simp [h, hp]

/-! The lemmas below are stated for any summands, so that the kernel
matches the instances of `∑` and `*` once, without unfolding the summands
(which made `lp_prodVal` take a second). -/

theorem coeff_sum (s : Finset Nat) (f : Nat → P) (p : Nat) :
    (∑ i ∈ s, f i).coeff p = ∑ i ∈ s, (f i).coeff p := finsetSum_coeff s f p

theorem eq_sum_of_coeff {a : P} {s : Finset Nat} {f : Nat → P}
    (h : ∀ p, a.coeff p = ∑ i ∈ s, (f i).coeff p) : a = ∑ i ∈ s, f i :=
  Polynomial.ext fun p => (h p).trans (coeff_sum s f p).symm

theorem coeff_mul_sums {a b : P} {f g : Nat → P} (ha : a = ∑ i ∈ Finset.range 8, f i)
    (hb : b = ∑ j ∈ Finset.range 4, g j) (p : Nat) :
    (a * b).coeff p = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 4, (f i * g j).coeff p := by
  subst ha hb; simp only [Finset.sum_mul_sum, finsetSum_coeff]

theorem lp_eq_sum_part (hv : BitVec 64) : lp hv = ∑ t ∈ Finset.range 8, lp (part hv t) := by
  refine eq_sum_of_coeff fun p => ?_
  rw [coeff_lp]
  simp only [coeff_lp, part, BitVec.getLsbD_and]
  by_cases hp : p < 64
  · rw [Finset.sum_eq_single (2 * (p % 4) + p / 32)]
    · rw [getLsbD_half (by omega) (by omega)]
      simp only [hp, true_and]
      rw [decide_eq_true (by omega), Bool.and_true]
    · intro t ht hne
      rw [getLsbD_half (by simp at ht; omega) (by omega)]
      rw [decide_eq_false (by omega), Bool.and_false]; rfl
    · intro h; simp at h; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp [bit]

theorem lp_eq_sum_cls (yv : BitVec 64) : lp yv = ∑ j ∈ Finset.range 4, lp (yv &&& cls j) := by
  refine eq_sum_of_coeff fun p => ?_
  rw [coeff_lp]
  simp only [coeff_lp, BitVec.getLsbD_and]
  by_cases hp : p < 64
  · rw [Finset.sum_eq_single (p % 4)]
    · rw [getLsbD_cls (by omega)]
      simp only [hp, true_and, decide_true, Bool.and_true]
    · intro j hj hne
      rw [getLsbD_cls (by simp at hj; omega), decide_eq_false (by omega), Bool.and_false]; rfl
    · intro h; simp at h; omega
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp [bit]

/-- `product` computes the carry-less product. -/
theorem lp_prodVal (hv yv : BitVec 64) : lp (prodVal hv yv) = lp hv * lp yv := by
  refine Polynomial.ext fun p => ?_
  by_cases hp : p < 128
  · rw [coeff_lp, getLsbD_prodVal hv yv hp,
      bit_classSum hv yv (p % 4) (Nat.mod_lt _ (by omega)) hp rfl 8 (Nat.le_refl _),
      coeff_mul_sums (lp_eq_sum_part hv) (lp_eq_sum_cls yv)]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_eq_single (jOf (p % 4) t)]
    · intro j hj hne
      simp only [Finset.mem_range] at ht hj
      refine coeff_lp_mul_sparse (sparse_part hv ht) (sparse_cls yv hj) ?_
      simp only [jOf] at hne; omega
    · intro h; simp [jOf] at h; omega
  · rw [coeff_lp, BitVec.getLsbD_of_ge _ _ (by omega), coeff_eq_zero_of_natDegree_lt]
    · rfl
    · have := (natDegree_mul_le (p := lp hv) (q := lp yv)).trans
        (Nat.add_le_add (natDegree_lp hv) (natDegree_lp yv))
      omega

/-- … which in SP 800-38D's bit order is `X · a · b`. -/
theorem gp_prodVal (hv yv : BitVec 64) : gp (prodVal hv yv) = X * gp hv * gp yv :=
  gp_of_lp (lp_prodVal hv yv)

end VG.Proof.Gcm.X86_64.Ctmul

end

section

/-!
# GHASH on x86-64: running a word product

Untrusted: everything here is checked by Lean. `Impl.Gcm.X86_64.product`
leaves `prodVal` of its factors in `r14:r13` (`product_ok`), changing no
other register but `rax, rdx, rbx, rbp, r9–r12`, and not memory.
-/

open VG.PowLit

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm.X86_64.Ctmul

/-- `s'` differs from `s` at most in the registers `clob` and the flags. -/
def Keeps (clob : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (clob : List Reg) (s : State) : Keeps clob s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {c : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps c s₁ s₂) (h₂ : Keeps c s₂ s₃) :
    Keeps c s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {c c' : List Reg} {s s' : State} (h : Keeps c s s') (hc : ∀ r ∈ c, r ∈ c') :
    Keeps c' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hc r h'), h.2⟩

/-- A load through a register the state keeps. -/
theorem Keeps.readSrc_mem {c : List Reg} {s s' : State} (h : Keeps c s s') {b : Reg} (hb : b ∉ c)
    (d : Nat) : readSrc s' (.mem (at_ b d)) = readSrc s (.mem (at_ b d)) := by
  simp only [readSrc, State.ea, at_, h.1 b hb]
  unfold State.load64
  rw [h.2.1, h.2.2.1, h.2.2.2]

/-- `mul` leaves the 128-bit product in `rdx:rax`. -/
theorem ofNat_split (p : Nat) : BitVec.ofNat 64 (p / 2 ^ 64) ++ BitVec.ofNat 64 p = BitVec.ofNat 128 p := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.Gcm.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## One product -/

/-- The registers one product changes. -/
abbrev termClob : List Reg := [.rax, .rdx, AL, AH]

set_option simprocs false in
theorem mulAcc_ok (d : Nat) (b : Reg) (hb : b ∉ termClob) (s : State) {c : BitVec 64}
    (hc : readSrc s (.mem (at_ .r8 d)) = some c) :
    WP isa (.block [.mov .rax (.mem (at_ .r8 d)), .mul b, .alu .xor AL (.reg .rax),
        .alu .xor AH (.reg .rdx)]) s fun s' =>
      s'.gpr AH ++ s'.gpr AL = (s.gpr AH ++ s.gpr AL) ^^^ ip c (s.gpr b) ∧ Keeps termClob s s' := by
  simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  have hc' : s.load64 (s.ea (at_ .r8 d)) = some c := hc
  apply WP.of_runBlock
  simp only [AL, AH] at h3 h4 ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execMul, readSrc, hc', isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false, h1,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← BitVec.xor_append, ofNat_split]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, AL, AH] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [r1, r2, r3, r4, ite_false]

theorem B_not_mem {j : Nat} : B j ∉ termClob ∧ B j ≠ PL ∧ B j ≠ PH ∧ B j ≠ .r8 ∧ B j ≠ W0 ∧
    B j ≠ .rsi ∧ B j ≠ .rdi ∧ B j ≠ .rcx ∧ B j ≠ .rsp := by
  unfold B; split <;> decide

theorem B_inj : ∀ i < 4, ∀ j < 4, B i = B j → i = j := by decide +kernel

/-- The table of `hv` is at `q`. -/
def Tbl (s : State) (q : Nat) (hv : BitVec 64) : Prop :=
  ∀ t < 8, readSrc s (.mem (at_ .r8 (off (8 * q + t)))) = some (part hv t)

theorem Tbl.keeps {c : List Reg} {s s' : State} {q : Nat} {hv : BitVec 64} (h : Tbl s q hv)
    (hk : Keeps c s s') (hc : Reg.r8 ∉ c) : Tbl s' q hv :=
  fun t ht => (hk.readSrc_mem hc _).trans (h t ht)

/-- The classes of `yv` are in the registers `B j`. -/
def Bs (s : State) (yv : BitVec 64) : Prop := ∀ j < 4, s.gpr (B j) = yv &&& cls j

theorem Bs.keeps {c : List Reg} {s s' : State} {yv : BitVec 64} (h : Bs s yv) (hk : Keeps c s s')
    (hc : ∀ j < 4, B j ∉ c) : Bs s' yv :=
  fun j hj => (hk.1 _ (hc j hj)).trans (h j hj)

/-! ## One class -/

/-- The registers a class changes. -/
abbrev clsClob : List Reg := [.rax, .rdx, AL, AH, PL, PH]

theorem term_ok {q k t : Nat} (ht : t < 8) {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hB : Bs s yv) :
    WP isa (.block (term q k t)) s fun s' =>
      s'.gpr AH ++ s'.gpr AL = (s.gpr AH ++ s.gpr AL) ^^^ ip (part hv t) (yv &&& cls (jOf k t)) ∧
      Keeps termClob s s' := by
  have hj : jOf k t < 4 := Nat.mod_lt _ (by omega)
  refine WP.mono (mulAcc_ok _ (B (jOf k t)) B_not_mem.1 s (hT t ht)) fun s' ⟨h1, h2⟩ => ⟨?_, h2⟩
  rw [h1, hB _ hj]

set_option simprocs false in
theorem zero_ok {lo hi : Reg} (h : lo ≠ hi) (s : State) :
    WP isa (.block [.mov lo (.imm 0), .mov hi (.imm 0)]) s fun s' =>
      s'.gpr hi ++ s'.gpr lo = (0 : BitVec 128) ∧ Keeps [lo, hi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    isa, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', h]
  refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

set_option simprocs false in
theorem mask_ok (k : Nat) (s : State) :
    WP isa (.block [.movImm64 .rax (cls k), .alu .and AL (.reg .rax), .alu .and AH (.reg .rax),
        .alu .xor PL (.reg AL), .alu .xor PH (.reg AH)]) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = (s.gpr PH ++ s.gpr PL) ^^^ ((s.gpr AH ++ s.gpr AL) &&& (cls k ++ cls k)) ∧
      Keeps clsClob s s' := by
  apply WP.of_runBlock
  simp only [AL, AH, PL, PH]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [← BitVec.xor_append, ← BitVec.and_append], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [clsClob, AL, AH, PL, PH, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, -, r3, r4, r5, r6⟩ := hr
  simp only [r1, r3, r4, r5, r6, ite_false]

theorem clsCode_ok {q k : Nat} {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hB : Bs s yv) :
    WP isa (.block (clsCode q k)) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = (s.gpr PH ++ s.gpr PL) ^^^ (classSum hv yv k 8 &&& (cls k ++ cls k)) ∧
      Keeps clsClob s s' := by
  rw [clsCode, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok (by decide) s) fun s₁ ⟨hz, hk₁⟩ => ?_
  have hT₁ := hT.keeps hk₁ (by decide)
  have hB₁ := hB.keeps hk₁ fun j _ => by
    have := (B_not_mem (j := j)).1
    simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, this.2.2.2⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun t s' => s'.gpr AH ++ s'.gpr AL = classSum hv yv k t ∧ Keeps termClob s₁ s')
    (fun t s' ht ⟨h₁, h₂⟩ => WP.mono (term_ok ht (hT₁.keeps h₂ (by decide))
      (hB₁.keeps h₂ fun j _ => B_not_mem.1)) fun s'' ⟨h₃, h₄⟩ =>
        ⟨by rw [h₃, h₁, classSum_succ], h₂.trans h₄⟩)
    8 (Nat.le_refl _) s₁ ⟨hz, Keeps.refl _ _⟩) fun s₂ ⟨h₁, h₂⟩ => ?_
  refine WP.mono (mask_ok k s₂) fun s₃ ⟨h₃, h₄⟩ => ⟨?_, ?_⟩
  · have hk : Keeps termClob s s₂ := (hk₁.mono (by decide)).trans h₂
    rw [h₃, h₁, hk.1 PL (by decide), hk.1 PH (by decide)]
  · exact ((hk₁.mono (by decide)).trans (h₂.mono (by decide))).trans h₄


/-! ## The product -/

/-- The registers the classes of the second factor are in. -/
abbrev Bregs : List Reg := [.rbx, .rbp, .r9, .r10]

/-- The registers a product changes. -/
abbrev prodClob : List Reg := [.rax, .rdx, .rbx, .rbp, .r9, .r10, AL, AH, PL, PH]

theorem B_mem (j : Nat) : B j ∈ Bregs := by unfold B; split <;> decide

theorem Keeps.setReg {c : List Reg} {s s' : State} (h : Keeps c s s') {r : Reg} (hr : r ∈ c)
    (v : BitVec 64) : Keeps c s (s'.setReg r v) :=
  ⟨fun r' hr' => by
    simp only [State.setReg]
    rw [ite_eq_right (fun (h' : r' = r) => hr' (h' ▸ hr))]
    exact h.1 r' hr', h.2⟩

set_option simprocs false in
theorem andCls_ok (b : Reg) (m : BitVec 64) (y : Src) (s : State) {yv : BitVec 64}
    (hy : ∀ v, readSrc (s.setReg b v) y = some yv) :
    WP isa (.block [.movImm64 b m, .alu .and b y]) s fun s' => s'.gpr b = yv &&& m ∧ Keeps [b] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hy, Option.bind_some, isa,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [State.setReg, arithFlags, State.setFlags, ite_true, BitVec.and_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [State.setReg, arithFlags, State.setFlags, ite_eq_right hr]

theorem split_ok (y : Src) (s : State) {yv : BitVec 64}
    (hy : ∀ s', Keeps Bregs s s' → readSrc s' y = some yv) :
    WP isa (.block (split y)) s fun s' => Bs s' yv ∧ Keeps Bregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4)
    (fun j s' => Keeps Bregs s s' ∧ ∀ i < j, s'.gpr (B i) = yv &&& cls i)
    (fun j s' hj ⟨h₁, h₂⟩ => WP.mono (andCls_ok (B j) (cls j) y s' fun v => hy _ (h₁.setReg (B_mem j) v))
      fun s'' ⟨h₃, h₄⟩ => ⟨h₁.trans (h₄.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr ▸ B_mem j), fun i hi => ?_⟩)
    4 (Nat.le_refl _) s ⟨Keeps.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s' ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
  by_cases hij : i = j
  · rw [hij, h₃]
  · rw [h₄.1 _ fun h => hij (B_inj i (by omega) j hj (by simpa using h)), h₂ i (by omega)]

/-- The first `n` classes of the product, masked and added. -/
def prodPart (hv yv : BitVec 64) (n : Nat) : BitVec 128 :=
  (List.range n).foldl (fun r k => r ^^^ (classSum hv yv k 8 &&& (cls k ++ cls k))) 0

theorem prodPart_succ (hv yv : BitVec 64) (n : Nat) :
    prodPart hv yv (n + 1) = prodPart hv yv n ^^^ (classSum hv yv n 8 &&& (cls n ++ cls n)) := by
  simp only [prodPart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `product` computes `prodVal` of the table `q` and `y`. -/
theorem product_ok (y : Src) (q : Nat) {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hy : ∀ s', Keeps Bregs s s' → readSrc s' y = some yv) :
    WP isa (.block (product y q)) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = prodVal hv yv ∧ Keeps prodClob s s' := by
  rw [product, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (split_ok y s hy) fun s₁ ⟨hB₁, hk₁⟩ => ?_
  refine WP.mono (zero_ok (by decide) s₁) fun s₂ ⟨hz, hk₂⟩ => ?_
  have hk : Keeps prodClob s s₂ := (hk₁.mono (by decide)).trans (hk₂.mono (by decide))
  have hT₂ := hT.keeps hk (by decide)
  have hB₂ := hB₁.keeps hk₂ fun j _ => by
    have := (B_not_mem (j := j))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this.2.1, this.2.2.1⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4)
    (fun k s' => s'.gpr PH ++ s'.gpr PL = prodPart hv yv k ∧ Keeps clsClob s₂ s')
    (fun k s' _ ⟨h₁, h₂⟩ => WP.mono (clsCode_ok (hT₂.keeps h₂ (by decide))
      (hB₂.keeps h₂ fun j _ => by
        have := (B_not_mem (j := j))
        simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
        exact ⟨this.1.1, this.1.2.1, this.1.2.2.1, this.1.2.2.2, this.2.1, this.2.2.1⟩))
      fun s'' ⟨h₃, h₄⟩ => ⟨by rw [h₃, h₁, prodPart_succ], h₂.trans h₄⟩)
    4 (Nat.le_refl _) s₂ ⟨hz, Keeps.refl _ _⟩) fun s₃ ⟨h₁, h₂⟩ => ⟨h₁, hk.trans (h₂.mono (by decide))⟩

end VG.Proof.Gcm.X86_64

end

section

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

open VG.PowLit

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
  have hb : ∀ d < 128, xInv.getMsbD d = (d = 0 || d = 1 || d = 6 || d = 127) := by decide +kernel
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

end

/-!
# GHASH on x86-64: running the other parts of the code

Untrusted: everything here is checked by Lean. What each straight-line
part of `Impl.Gcm.X86_64.ghash` other than `product` does, one symbolic
execution each.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm.X86_64.Ctmul

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- `s'` differs from `s` at most in the registers `clob`, the flags and memory. -/
def Regs (clob : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.regs {c : List Reg} {s s' : State} (h : Keeps c s s') : Regs c s s' := ⟨h.1, h.2.2⟩

theorem Regs.trans {c : List Reg} {s₁ s₂ s₃ : State} (h₁ : Regs c s₁ s₂) (h₂ : Regs c s₂ s₃) :
    Regs c s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Regs.mono {c c' : List Reg} {s s' : State} (h : Regs c s s') (hc : ∀ r ∈ c, r ∈ c') :
    Regs c' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hc r h'), h.2⟩

/-- The registers `load` changes. -/
abbrev loadClob : List Reg := [W0, .rax, AL]

set_option simprocs false in
theorem load_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hy8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (hx0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hx8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (wm : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((240 : Nat) : Int)) 8) :
    WP isa (.block load) s fun s' =>
      s'.gpr W0 = bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ^^^
        bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ∧
      s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int))
          (bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64))).writeW
        (s.gpr .r8 + BitVec.ofInt 64 ((240 : Nat) : Int))
          ((bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)) ^^^
          (bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64))) ∧
      Regs loadClob s s' := by
  apply WP.of_runBlock
  simp only [load, W0, AL, slotM]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.store64, State.setReg, arithFlags, State.setFlags,
    hy0, hy8, hx0, hx8, wy8, wm, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [loadClob, W0, AL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3⟩ := hr
  simp only [r1, r2, r3, ite_false]

set_option simprocs false in
theorem keepA_ok (s : State) (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8) :
    WP isa (.block keepA) s fun s' =>
      s'.gpr W0 = s.gpr PH ∧
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) (s.gpr PL) ∧
      Regs [W0] s s' := by
  apply WP.of_runBlock
  simp only [keepA, W0, PH, PL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, ea_at, State.store64, State.setReg, wy0, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

set_option simprocs false in
theorem keepB_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (ww : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 8) :
    WP isa (.block keepB) s fun s' =>
      s'.mem = ((s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int))
          ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH) ^^^ s.gpr W0)).writeW
          (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int))
          ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH) ^^^ s.gpr PL)).writeW
        (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) (s.gpr PL) ∧
      Regs [.rax, AL] s s' := by
  apply WP.of_runBlock
  simp only [keepB, W0, AL, PH, PL, slotW]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.store64, State.setReg, arithFlags, State.setFlags,
    hy0, wy0, wy8, ww, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

set_option simprocs false in
theorem keepM_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hy8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (hw : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 8) :
    WP isa (.block keepM) s fun s' =>
      s'.gpr AL = s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH ∧
      s'.gpr AH = s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64 ^^^ s.gpr PL ∧
      s'.gpr PL = s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 64 ∧
      Keeps [AL, AH, PL] s s' := by
  apply WP.of_runBlock
  simp only [keepM, AL, AH, PH, PL, slotW]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.setReg, arithFlags, State.setFlags,
    hy0, hy8, hw, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3⟩ := hr
  simp only [r1, r2, r3, ite_false]

theorem rot_mask (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) (c : BitVec 32)
    (hc : c.signExtend 64 = BitVec.ofNat 64 (2 ^ s - 1)) :
    (w &&& c.signExtend 64).rotateRight s = w <<< (64 - s) := by
  rw [hc]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt hs']
  have hm : ∀ j, (BitVec.ofNat 64 (2 ^ s - 1)).getLsbD j = decide (j < s) := by
    intro j
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < s
    · simp [hj, show j < 64 by omega]
    · simp [hj]
  by_cases h : i < 64 - s
  · rw [ite_eq_left h, BitVec.getLsbD_and, hm, decide_eq_false (by omega), Bool.and_false]
    simp [h, hi]
  · rw [ite_eq_right h, BitVec.getLsbD_and, hm, decide_eq_true (show i - (64 - s) < s by omega)]
    simp [h, hi]

set_option simprocs false in
theorem fold_ok (w lo hi : Reg) (h1 : w ≠ .rax) (h2 : lo ≠ .rax) (h3 : hi ≠ .rax) (h4 : w ≠ lo)
    (h5 : w ≠ hi) (h6 : lo ≠ hi) (s : State) :
    WP isa (.block (fold w lo hi)) s fun s' =>
      s'.gpr lo = foldLo (s.gpr lo) (s.gpr w) ∧ s'.gpr hi = foldHi (s.gpr hi) (s.gpr w) ∧
      Keeps [.rax, lo, hi] s s' := by
  apply WP.of_runBlock
  have n1 : w = .rax ↔ False := iff_false_intro h1
  have n2 : lo = .rax ↔ False := iff_false_intro h2
  have n3 : hi = .rax ↔ False := iff_false_intro h3
  have n4 : w = lo ↔ False := iff_false_intro h4
  have n5 : w = hi ↔ False := iff_false_intro h5
  have n6 : lo = hi ↔ False := iff_false_intro h6
  have n7 : hi = lo ↔ False := iff_false_intro (Ne.symm h6)
  simp (config := {decide := true}) only [fold, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, isa, State.setReg, arithFlags, State.setFlags, n1, n2, n3, n4, n5,
    n6, n7, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [rot_mask _ (s := 1) (by omega) (by omega) _ (by decide),
      rot_mask _ (s := 2) (by omega) (by omega) _ (by decide),
      rot_mask _ (s := 7) (by omega) (by omega) _ (by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3⟩ := hr
    simp only [r1, r2, r3, ite_false]

set_option simprocs false in
theorem store_ok (s : State)
    (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) (bswap64 (s.gpr W0))).writeW
        (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) (bswap64 (s.gpr AL)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      Regs [W0, AL, .rdi, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [store, W0, AL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.store64, State.setReg, arithFlags, State.setFlags, wy0, wy8,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨by trivial, by rw [e16], by rw [e1], by rw [e1], fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3, r4⟩ := hr
  simp only [r1, r2, r3, r4, ite_false]


/-! ## The set-up -/

theorem mask_xInv (a b : BitVec 64) (c : Bool) :
    (a ^^^ (xInvHigh &&& if c then BitVec.allOnes 64 else 0#64)) ++
      (b ^^^ ((if c then BitVec.allOnes 64 else 0#64) &&& BitVec.signExtend 64 (1 : BitVec 32))) =
      (a ++ b) ^^^ (if c then xInv else 0) := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, BitVec.and_zero, BitVec.zero_and, BitVec.xor_zero]
    exact (BitVec.xor_zero (x := a ++ b)).symm
  · simp only [ite_true, BitVec.and_allOnes, BitVec.allOnes_and, xInv, ← BitVec.xor_append]
    rfl

set_option simprocs false in
theorem hInv_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block hInv) s fun s' =>
      s'.gpr AL ++ s'.gpr AH =
        ((bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)) <<< 1) ^^^
          (if (bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)).getMsbD 0
          then xInv else 0) ∧
      s'.gpr PH = s'.gpr AL ^^^ s'.gpr AH ∧ Keeps [AL, AH, .rax, PL, PH] s s' := by
  apply WP.of_runBlock
  simp only [hInv, AL, AH, PL, PH]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.setReg, arithFlags, State.setFlags, h0, h8,
    ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · rw [sbb_self, shl1_cf, mask_xInv, shl1, BitVec.msb_eq_getMsbD_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    simp only [r1, r2, r3, r4, r5, ite_false]

theorem tblReg_ne (q : Nat) : tblReg q ≠ .rax := by unfold tblReg; split <;> decide

set_option simprocs false in
theorem entry_ok (u : Nat) (s : State)
    (hw : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((off u : Nat) : Int)) 8) :
    WP isa (.block (entry u)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofInt 64 ((off u : Nat) : Int))
        (s.gpr (tblReg (u / 8)) &&& half (u % 8 / 2) (u % 2)) ∧ Regs [.rax] s s' := by
  have hn : tblReg (u / 8) = .rax ↔ False := iff_false_intro (tblReg_ne _)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [entry, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, isa, ea_at, State.store64, State.setReg, arithFlags, State.setFlags, hw, hn,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.and_comm], fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

set_option simprocs false in
theorem tail_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx), .alu .test .rcx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rdx ∧ s'.zf = some (s.gpr .rcx &&& s.gpr .rcx == 0) ∧
      Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

end VG.Proof.Gcm.X86_64
