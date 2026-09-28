import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Reverse
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Impl.Gcm.X86_64

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
    (half i h).getLsbD p = decide (p % 4 = i ∧ p / 32 = h) := by decide

theorem getLsbD_cls_lt : ∀ p < 64, ∀ j < 4, (cls j).getLsbD p = decide (p % 4 = j) := by decide

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
      bit_classSum hv yv (p % 4) (Nat.mod_lt _ (by omega)) hp rfl 8 le_rfl,
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
