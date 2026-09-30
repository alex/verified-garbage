import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Reverse
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Impl.Gcm.X86_64
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86_64.Parts`.
section

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
  · simp only [h, ↓reduceIte, BitVec.getLsbD_eq_getElem]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_of_ge v k (by omega_using [h]), Bool.false_eq_true]

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
  rw [coeff_lp, BitVec.getLsbD_of_ge v N (by omega_using [hN])]
  rfl

/-- `gp` is `lp` read backwards. -/
theorem gp_eq_reflect {n : Nat} (hn : 0 < n) (v : BitVec n) : gp v = reflect (n - 1) (lp v) := by
  ext k
  rw [coeff_reflect, coeff_gp]
  by_cases hk : k ≤ n - 1
  · rw [revAt_le hk, coeff_lp, BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega_using [hn, hk]), Bool.true_and]
  · rw [revAt_eq_self_of_lt (by omega_using [hk]), coeff_lp, BitVec.getLsbD_of_ge v k (by omega_using [hn, hk])]
    simp only [BitVec.getMsbD, show ¬k < n by omega_using [hn, hk], decide_false, Bool.false_and]

/-- A 128-bit word whose `lp` is the product of two words' is their product
in the reflected order, with a factor `X`. -/
theorem gp_of_lp {r : BitVec 128} {a b : BitVec 64} (h : lp r = lp a * lp b) :
    gp r = X * gp a * gp b := by
  rw [gp_eq_reflect (by decide), gp_eq_reflect (by decide), gp_eq_reflect (by decide), h,
    show (128 - 1 : Nat) = 1 + (63 + 63) by rfl, ← one_mul (lp a * lp b),
    reflect_mul _ _ (natDegree_one.le.trans (Nat.zero_le 1))
      ((natDegree_mul_le).trans (Nat.add_le_add (natDegree_lp a) (natDegree_lp b))),
    reflect_mul _ _ (natDegree_lp a) (natDegree_lp b)]
  simp only [reflect_one, pow_one, Nat.add_one_sub_one, mul_assoc]

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
    omega_using [e, this]
  | succ w ih =>
    have e := congrArg (eval 16) (divX_mul_X_add F)
    simp only [eval_add, eval_mul, eval_X, eval_C] at e
    have := hF 0
    have h16 : F.eval 16 / 16 = (divX F).eval 16 := by rw [← e]; omega_using [e, this]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, h16, ih _ fun w => by rw [coeff_divX]; exact hF _,
      coeff_divX]

theorem testBit_eval (F : ℕ[X]) (hF : ∀ w, F.coeff w < 16) (e w s : Nat) (hs : s < 4) :
    (2 ^ e * F.eval 16).testBit (e + 4 * w + s) = (F.coeff w).testBit s := by
  rw [Nat.testBit_two_pow_mul, decide_eq_true (by omega_using [hs]), Bool.true_and,
    show e + 4 * w + s - e = s + 4 * w by omega_using [hs], ← Nat.testBit_div_two_pow, pow_mul,
    show (2 : Nat) ^ 4 = 16 by rfl, ← eval_digit F hF w, show (16 : Nat) = 2 ^ 4 by rfl,
    Nat.testBit_mod_two_pow, decide_eq_true hs, Bool.true_and]

theorem testBit_eval_lt (F : ℕ[X]) {e p : Nat} (hp : p < e) : (2 ^ e * F.eval 16).testBit p = false := by
  rw [Nat.testBit_two_pow_mul, decide_eq_false (by omega_using [hp]), Bool.false_and]

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
  rw [coeff_sp]; split_ifs <;> omega_using []

/-- The bits of `v` are among `e + 4u`, `u < m`. -/
def Sparse (v : BitVec 64) (e m : Nat) : Prop :=
  ∀ p, v.getLsbD p = true → e ≤ p ∧ (p - e) % 4 = 0 ∧ p < e + 4 * m

theorem toNat_sparse {v : BitVec 64} {e m : Nat} (h : Sparse v e m) :
    v.toNat = 2 ^ e * (sp v e m).eval 16 := by
  have hF : ∀ w, (sp v e m).coeff w < 16 := fun w => by have := coeff_sp_le v e m w; omega_using [this]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [BitVec.testBit_toNat]
  by_cases hp : p < e
  · rw [testBit_eval_lt _ hp]
    cases hv : v.getLsbD p
    · rfl
    · have := h p hv; omega_using [hp, this]
  · obtain ⟨w, s, hs, rfl⟩ : ∃ w s, s < 4 ∧ p = e + 4 * w + s :=
      ⟨(p - e) / 4, (p - e) % 4, Nat.mod_lt _ (by decide), by omega_using [hp]⟩
    rw [testBit_eval _ hF _ _ _ hs, coeff_sp]
    by_cases hs0 : s = 0
    · subst hs0
      rw [Nat.add_zero]
      by_cases hw : w < m
      · cases hv : v.getLsbD (e + 4 * w) <;> simp [hw]
      · cases hv : v.getLsbD (e + 4 * w)
        · simp only [Bool.false_eq_true, and_false, ↓reduceIte, Nat.testBit_zero, Nat.zero_mod, zero_ne_one, decide_false]
        · have := h _ hv; omega_using [hw, this]
    · have e0 : v.getLsbD (e + 4 * w + s) = false := by
        cases hv : v.getLsbD (e + 4 * w + s)
        · rfl
        · have := h _ hv; omega_using [hs, hp, hs0, this]
      rw [e0]
      split_ifs
      · rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hs0)]
      · simp only [Nat.zero_testBit]


/-- A word with holes, over `GF(2)`. -/
theorem lp_sparse {v : BitVec 64} {e m : Nat} (h : Sparse v e m) :
    lp v = X ^ e * expand (ZMod 2) 4 ((sp v e m).map (Nat.castRingHom (ZMod 2))) := by
  ext k
  rw [coeff_lp, coeff_X_pow_mul', coeff_expand (by decide), coeff_map, coeff_sp]
  cases hv : v.getLsbD k
  · split_ifs with h1 h2 h3
    · rw [show e + 4 * ((k - e) / 4) = k by omega_using [h1, h2], hv] at h3
      simp only [Bool.false_eq_true, and_false] at h3
    all_goals simp [bit]
  · obtain ⟨h1, h2, h3⟩ := h k hv
    rw [ite_eq_left h1, ite_eq_left (Nat.dvd_of_mod_eq_zero h2), ite_eq_left ⟨by omega_using [h1, h2, h3],
      by rw [show e + 4 * ((k - e) / 4) = k by omega_using [h1, h2]]; exact hv⟩]
    simp only [bit, ↓reduceIte, eq_natCast, Nat.cast_one]

/-- Sums of at most `m` bits. -/
theorem sum_range_ite_le (f : Nat → Nat) (hf : ∀ k, f k ≤ 1) (m : Nat) (hm : ∀ k, m ≤ k → f k = 0) :
    ∀ n, ∑ k ∈ Finset.range n, f k ≤ m := by
  have : ∀ n, ∑ k ∈ Finset.range n, f k ≤ min n m := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_le, inf_of_le_left, Std.le_refl]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : m ≤ n
      · rw [hm n h]; omega_using [ih, h]
      · have := hf n; omega_using [ih, h, this]
  exact fun n => (this n).trans (Nat.min_le_right _ _)

/-- The column sums of the product of two words with holes, one of them with
at most `m` bits. -/
theorem coeff_sp_mul_le (a b : BitVec 64) (ea eb m mb w : Nat) :
    (sp a ea m * sp b eb mb).coeff w ≤ m := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (Finset.sum_le_sum fun k _ => ?_).trans
    (sum_range_ite_le (fun k => (sp a ea m).coeff k) (coeff_sp_le a ea m) m
      (fun k hk => by rw [coeff_sp, ite_eq_right (by omega_using [hk])]) _)
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
  · rw [testBit_eval_lt _ hlt, ite_eq_right (by omega_using [hpc, hlt])]; rfl
  · obtain ⟨w, rfl⟩ : ∃ w, p = ea + eb + 4 * w := ⟨(p - (ea + eb)) / 4, by omega_using [hpc, hlt]⟩
    rw [show ea + eb + 4 * w = ea + eb + 4 * w + 0 by rfl, testBit_eval _ hF _ _ _ (by decide),
      ite_eq_left (by omega_using [hpc]), show ea + eb + 4 * w + 0 - (ea + eb) = 4 * w by omega_using [hpc],
      coeff_expand (by decide), ite_eq_left (Dvd.intro w rfl), Nat.mul_div_cancel_left _ (by decide),
      coeff_map, bit_testBit_zero]
    rfl

/-- … and the carry-less product has no bits at the other positions. -/
theorem coeff_lp_mul_sparse {a b : BitVec 64} {ea ma eb mb : Nat} (ha : Sparse a ea ma)
    (hb : Sparse b eb mb) {p : Nat} (hpc : p % 4 ≠ (ea + eb) % 4) : (lp a * lp b).coeff p = 0 := by
  rw [lp_sparse ha, lp_sparse hb,
    show ∀ f g : P, X ^ ea * f * (X ^ eb * g) = X ^ (ea + eb) * (f * g) by intros; ring,
    coeff_X_pow_mul', ← map_mul, coeff_expand (by decide)]
  split_ifs with h1 h2
  · omega_using [hpc, h1, h2]
  · rfl
  · rfl


/-! ## The masks -/

theorem getLsbD_half_lt : ∀ p < 64, ∀ i < 4, ∀ h < 2,
    (half i h).getLsbD p = decide (p % 4 = i ∧ p / 32 = h) := by decide +kernel

theorem getLsbD_cls_lt : ∀ p < 64, ∀ j < 4, (cls j).getLsbD p = decide (p % 4 = j) := by decide +kernel

theorem getLsbD_half {i h : Nat} (hi : i < 4) (hh : h < 2) (p : Nat) :
    (half i h).getLsbD p = decide (p < 64 ∧ p % 4 = i ∧ p / 32 = h) := by
  by_cases hp : p < 64
  · rw [getLsbD_half_lt p hp i hi h hh]; simp only [Bool.decide_and, hp, true_and]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hp])]; simp only [hp, false_and, decide_false]

theorem getLsbD_cls {j : Nat} (hj : j < 4) (p : Nat) :
    (cls j).getLsbD p = decide (p < 64 ∧ p % 4 = j) := by
  by_cases hp : p < 64
  · rw [getLsbD_cls_lt p hp j hj]; simp only [hp, true_and]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hp])]; simp only [hp, false_and, decide_false]

/-- Part `t` of the first factor. -/
def part (hv : BitVec 64) (t : Nat) : BitVec 64 := hv &&& half (t / 2) (t % 2)

/-- The class of the second factor that part `t` meets in class `k`. -/
def jOf (k t : Nat) : Nat := (k + 4 - t / 2) % 4

theorem sparse_part (hv : BitVec 64) {t : Nat} (ht : t < 8) : Sparse (part hv t) (t / 2 + 32 * (t % 2)) 8 := by
  intro p hp
  rw [part, BitVec.getLsbD_and, getLsbD_half (by omega_using [ht]) (by omega_using [])] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  omega_using [ht, hp]

theorem sparse_cls (yv : BitVec 64) {j : Nat} (hj : j < 4) : Sparse (yv &&& cls j) j 16 := by
  intro p hp
  rw [BitVec.getLsbD_and, getLsbD_cls hj] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  omega_using [hj, hp]

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
  | zero => simp only [bit, classSum, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, BitVec.getLsbD_zero, Bool.false_eq_true, ↓reduceIte, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [classSum_succ, BitVec.getLsbD_xor, bit_xor, ih (by omega_using [hn]), Finset.sum_range_succ,
      bit_ip (sparse_part hv (by omega_using [hn])) (sparse_cls yv (by simp only [jOf]; omega_using [])) (by decide) hp
        (by simp only [jOf]; omega_using [hk, hpk, hn])]

theorem getLsbD_mask {k : Nat} (hk : k < 4) (p : Nat) :
    (cls k ++ cls k).getLsbD p = decide (p < 128 ∧ p % 4 = k) := by
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · rw [getLsbD_cls hk]; simp only [h, true_and, decide_eq_decide]; omega_using [h]
  · rw [getLsbD_cls hk]; simp only [decide_eq_decide]; omega_using [hk, h]

theorem getLsbD_prodVal (hv yv : BitVec 64) {p : Nat} (hp : p < 128) :
    (prodVal hv yv).getLsbD p = (classSum hv yv (p % 4) 8).getLsbD p := by
  simp only [prodVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_mask (show 0 < 4 by decide), getLsbD_mask (show 1 < 4 by decide),
    getLsbD_mask (show 2 < 4 by decide), getLsbD_mask (show 3 < 4 by decide)]
  have : p % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (by omega_using [this] : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3) with h | h | h | h <;>
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
    · rw [getLsbD_half (by omega_using [hp]) (by omega_using [])]
      simp only [hp, true_and]
      rw [decide_eq_true (by omega_using [hp]), Bool.and_true]
    · intro t ht hne
      rw [getLsbD_half (by simp only [Finset.mem_range] at ht; omega_using [ht]) (by omega_using [])]
      rw [decide_eq_false (by omega_using [hne]), Bool.and_false]; rfl
    · intro h; simp only [Finset.mem_range, not_lt] at h; omega_using [hp, h]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hp])]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Finset.sum_const_zero]

theorem lp_eq_sum_cls (yv : BitVec 64) : lp yv = ∑ j ∈ Finset.range 4, lp (yv &&& cls j) := by
  refine eq_sum_of_coeff fun p => ?_
  rw [coeff_lp]
  simp only [coeff_lp, BitVec.getLsbD_and]
  by_cases hp : p < 64
  · rw [Finset.sum_eq_single (p % 4)]
    · rw [getLsbD_cls (by omega_using [])]
      simp only [hp, true_and, decide_true, Bool.and_true]
    · intro j hj hne
      rw [getLsbD_cls (by simp only [Finset.mem_range] at hj; omega_using [hj]), decide_eq_false (by omega_using [hne]), Bool.and_false]; rfl
    · intro h; simp only [Finset.mem_range, not_lt] at h; omega_using [h]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hp])]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Finset.sum_const_zero]

/-- `product` computes the carry-less product. -/
theorem lp_prodVal (hv yv : BitVec 64) : lp (prodVal hv yv) = lp hv * lp yv := by
  refine Polynomial.ext fun p => ?_
  by_cases hp : p < 128
  · rw [coeff_lp, getLsbD_prodVal hv yv hp,
      bit_classSum hv yv (p % 4) (Nat.mod_lt _ (by decide)) hp rfl 8 (Nat.le_refl _),
      coeff_mul_sums (lp_eq_sum_part hv) (lp_eq_sum_cls yv)]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_eq_single (jOf (p % 4) t)]
    · intro j hj hne
      simp only [Finset.mem_range] at ht hj
      refine coeff_lp_mul_sparse (sparse_part hv ht) (sparse_cls yv hj) ?_
      simp only [jOf] at hne; omega_using [hne, ht, hj]
    · intro h; simp only [jOf, Finset.mem_range, not_lt] at h; omega_using [h]
  · rw [coeff_lp, BitVec.getLsbD_of_ge _ _ (by omega_using [hp]), coeff_eq_zero_of_natDegree_lt]
    · rfl
    · have := (natDegree_mul_le (p := lp hv) (q := lp yv)).trans
        (Nat.add_le_add (natDegree_lp hv) (natDegree_lp yv))
      omega_using [hp, this]

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
  omega_using []

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
    execMul, readSrc, hc', isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, Keeps, and_true, ite_true, ite_false, h1,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_⟩
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
  have hj : jOf k t < 4 := Nat.mod_lt _ (by decide)
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
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Keeps, and_true, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [← BitVec.xor_append, ← BitVec.and_append], fun r hr => ?_⟩
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
  · rw [h₄.1 _ fun h => hij (B_inj i (by omega_using [hj, hi]) j hj (by simpa using h)), h₂ i (by omega_using [hi, hij])]

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
    · simp only [ite_eq_left h1, ite_eq_left h2, decide_eq_false (show ¬ d < 64 by omega_using [h2]),
        Bool.false_and, show d - 64 + (64 - s) = d - s by omega_using [hs, hs', h1, h2]]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_add]
    · simp only [ite_eq_left h1, ite_eq_right h2, decide_eq_true (show d < 64 by omega_using [h2]),
        decide_eq_false (show ¬ d < s by omega_using [h1]), Bool.not_false, Bool.true_and, add_zero]
  · simp only [ite_eq_right h1, ite_eq_right (show ¬ 64 ≤ d by omega_using [hs, hs', h1]),
      decide_eq_true (show d < s by omega_using [h1]), Bool.not_true, Bool.false_and, Bool.and_false, add_zero]
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
  have e1 := ψ_shr_shl w (s := 1) (by decide) (by decide)
  have e2 := ψ_shr_shl w (s := 2) (by decide) (by decide)
  have e7 := ψ_shr_shl w (s := 7) (by decide) (by decide)
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
    rcases (by omega_using [] : d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 127 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h6, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, h7, Bool.false_eq_true, ↓reduceIte, show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInv.getMsbD d = false := BitVec.getMsbD_of_ge _ _ (by omega_using [hd])
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega_using [hd], show (1 : Nat) ≠ d by omega_using [hd], add_zero, show d ≠ 6 by omega_using [hd], show d ≠ 127 by omega_using [hd]]

theorem x_φ_xInv : x * φ xInv = 1 := by
  simp only [φ, gp_xInv, map_add, map_one, map_pow, AdjoinRoot.mk_X]
  linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q

theorem gp_shl1 (h : BitVec 128) : X * gp (h <<< 1) + C (bit (h.getMsbD 0)) = gp h := by
  ext d
  rw [coeff_add, coeff_C, coeff_gp]
  rcases d with _ | d
  · simp only [mul_coeff_zero, coeff_X_zero, zero_mul, ↓reduceIte, zero_add]
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]; simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]

/-- `hInv`'s result is `x⁻¹ · H`. -/
theorem x_φ_hInv (h : BitVec 128) :
    x * φ ((h <<< 1) ^^^ (if h.getMsbD 0 then xInv else 0)) = φ h := by
  have e := congrArg (AdjoinRoot.mk g) (gp_shl1 h)
  simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at e
  rw [φ_xor, mul_add]
  change x * AdjoinRoot.mk g (gp (h <<< 1)) + _ = AdjoinRoot.mk g (gp h)
  rw [← e]
  split_ifs with hb
  · rw [x_φ_xInv, hb]; simp only [bit, ↓reduceIte, map_one]
  · rw [φ_zero, Bool.not_eq_true] at *; rw [hb]; simp only [mul_zero, add_zero, bit, Bool.false_eq_true, ↓reduceIte, map_zero]

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
    readSrc, isa, ea_at, State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Regs, and_true,
    hy0, hy8, hx0, hx8, wy8, wm, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_⟩
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
    readSrc, isa, ea_at, State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Regs, and_true,
    hy0, wy0, wy8, ww, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun r hr => ?_⟩
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
    readSrc, isa, ea_at, State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Keeps, and_true,
    hy0, hy8, hw, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, by trivial, fun r hr => ?_⟩
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
    · simp only [show j < 64 by omega_using [hs, hs', hj], decide_true, hj, Bool.and_self]
    · simp only [hj, decide_false, Bool.and_false]
  by_cases h : i < 64 - s
  · rw [ite_eq_left h, BitVec.getLsbD_and, hm, decide_eq_false (by omega_using [hi]), Bool.and_false]
    simp only [hi, decide_true, h, Bool.not_true, Bool.and_false, Bool.false_and]
  · rw [ite_eq_right h, BitVec.getLsbD_and, hm, decide_eq_true (show i - (64 - s) < s by omega_using [hs, hs', hi, h])]
    simp only [hi, decide_true, Bool.and_true, Bool.true_and, h, decide_false, Bool.not_false, Bool.and_self]

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
    execAlu, execShift, readSrc, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
    RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, Keeps, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, and_true, n1, n2, n3, n4, n5,
    n6, n7, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, ?_, fun r hr => ?_⟩
  · rw [rot_mask _ (s := 1) (by decide) (by decide) _ (by decide),
      rot_mask _ (s := 2) (by decide) (by decide) _ (by decide),
      rot_mask _ (s := 7) (by decide) (by decide) _ (by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3⟩ := hr
    simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, r1, r2, r3,
      not_false_eq_true]

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
    readSrc, isa, ea_at, State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Keeps,
    and_true, h0, h8,
    ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by trivial, fun r hr => ?_⟩
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
    execAlu, readSrc, isa, ea_at, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Regs, and_true, hw, hn,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.and_comm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

set_option simprocs false in
theorem tail_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx), .alu .test .rcx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rdx ∧ s'.zf = some (s.gpr .rcx &&& s.gpr .rcx == 0) ∧
      Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, Keeps, and_true, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

end VG.Proof.Gcm.X86_64

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.X86_64.Ghash`.
section

/-!
# GHASH on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`:
replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over the `n`
blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other, the other
buffers, or the return address on the stack. The pointers and `n` are
public; `H`, `Y` and the data are secret. -/
def ghashX86_64 : Contract X86_64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .rdi, 16⟩
    let y : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ ret.Disjoint y ∧ ret.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .rsi) =
      ghashFrom (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
        (blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

end VG.Proof.Gcm

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm VG.Proof.Gcm.X86_64.Ctmul VG.Proof.Gcm.Poly
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp only [BitVec.ofInt_natCast]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .rdi
abbrev yp : Addr := s₀.gpr .rsi
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, zero_add, Nat.one_le_ofNat]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨hR s₀, by simp only [h.rd, List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀, true_or], contains_offset' hd (by omega)⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨yR s₀, by simp only [h.wr, List.mem_append, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_self, or_false, or_true], contains_offset' hd (by omega)⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨yR s₀, by simp only [h.wr, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_self, or_false], contains_offset' hd (by omega)⟩

theorem in_save {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp only [h.wr, List.mem_append, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_false, or_true], contains_offset' hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp only [h.wr, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_false, or_true], contains_offset' hd (by omega)⟩

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) := by
  have := h.nb_lt
  exact sub_offset (by omega) (by omega)

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp only [h.rd, List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, true_or, or_true], ?_⟩
  rw [ofInt_natCast, blkAddr, Offset.add_add]
  exact contains_offset (by omega) (by omega)

end Pre


/-! ## Separation in `y` and `scratch` -/

theorem off_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) (64 / 8) (p + BitVec.ofInt 64 (e : Int)) (64 / 8) := by
  rw [ofInt_natCast, ofInt_natCast]; exact Offset.sep p h (by omega) (by omega)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he h) (by decide)

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem sep_ys {d e : Nat} (hd : d + 8 ≤ 16) (he : e + 8 ≤ 256) :
    Mem.Sep (yp s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) (scr s₀ + BitVec.ofInt 64 (e : Int)) (64 / 8) :=
  h.y_scr.sep (contains_offset' hd (by omega)) (contains_offset' he (by omega))

theorem sep_sy {d e : Nat} (hd : d + 8 ≤ 256) (he : e + 8 ≤ 16) :
    Mem.Sep (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) (yp s₀ + BitVec.ofInt 64 (e : Int)) (64 / 8) :=
  h.y_scr.symm.sep (contains_offset' hd (by omega)) (contains_offset' he (by omega))

theorem readW_y_s (m : Mem) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 16) (he : e + 8 ≤ 256) :
    (m.writeW (scr s₀ + BitVec.ofInt 64 (e : Int)) v).readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (h.sep_ys hd he) (by decide)

theorem readW_s_y (m : Mem) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 256) (he : e + 8 ≤ 16) :
    (m.writeW (yp s₀ + BitVec.ofInt 64 (e : Int)) v).readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (h.sep_sy hd he) (by decide)

end Pre

/-! ## Memory while hashing -/

/-- Where `Y_A ⊕ Y_B` and `W₃` are kept. -/
abbrev slotR (s₀ : State) : Region := ⟨scr s₀ + BitVec.ofNat 64 240, 16⟩

theorem slot_contains (s₀ : State) {d : Nat} (hd : 240 ≤ d) (hd' : d + 8 ≤ 256) :
    (slotR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) := by
  rw [ofInt_natCast]
  exact Offset.contains _ hd (by omega) (by decide)

theorem slot_disjoint (s₀ : State) {d : Nat} (hd : d + 8 ≤ 240) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 64 / 8⟩ (slotR s₀) := by
  rw [ofInt_natCast]
  exact Offset.disjoint _ (Or.inl hd) (by omega) (by decide)

/-- Memory outside `y` and `scratch` is as on entry, and memory outside `y`
and the slots as after the set-up (`mS`). -/
structure MemInv (s₀ : State) (mS m : Mem) : Prop where
  f1 : Frame [yR s₀, scrR s₀] s₀.mem m
  f2 : Frame [yR s₀, slotR s₀] mS m

theorem MemInv.write_y {s₀ : State} {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat} (hd : d + 8 ≤ 16)
    (v : BitVec 64) : MemInv s₀ mS (m.writeW (yp s₀ + BitVec.ofInt 64 (d : Int)) v) :=
  ⟨h.f1.writeW (List.mem_cons_self ..) _ (contains_offset' hd (by omega)),
    h.f2.writeW (List.mem_cons_self ..) _ (contains_offset' hd (by omega))⟩

theorem MemInv.write_slot {s₀ : State} {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat} (hd : 240 ≤ d)
    (hd' : d + 8 ≤ 256) (v : BitVec 64) : MemInv s₀ mS (m.writeW (scr s₀ + BitVec.ofInt 64 (d : Int)) v) :=
  ⟨h.f1.writeW (by simp only [List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_false, or_true]) _ (contains_offset' hd' (by omega)),
    h.f2.writeW (by simp only [List.mem_cons, Region.mk.injEq, and_true, List.not_mem_nil, or_false, or_true]) _ (slot_contains s₀ hd hd')⟩

/-- `scratch` below the slots is as after the set-up. -/
theorem MemInv.readW_low {s₀ : State} (hp : Pre s₀) {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat}
    (hd : d + 8 ≤ 240) :
    m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 = mS.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
  refine h.f2.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine hp.y_scr.symm.sub_left ?_
    rw [ofInt_natCast]
    exact sub_offset (by omega) (by omega)
  · exact slot_disjoint s₀ hd

/-- The words of the three tables. -/
def hword (ka kb : BitVec 64) : Nat → BitVec 64
  | 0 => ka
  | 1 => kb
  | _ => ka ^^^ kb

/-- The tables of `H' = ka ‖ kb` are in `m` at `p`. -/
def TblMem (p : Addr) (ka kb : BitVec 64) (m : Mem) : Prop :=
  ∀ u < 24, m.readW (p + BitVec.ofInt 64 ((off u : Nat) : Int)) 64 = part (hword ka kb (u / 8)) (u % 8)

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) 64 = s₀.gpr .r15

/-- What the set-up leaves in memory. -/
structure SetupMem (s₀ : State) (ka kb : BitVec 64) (mS : Mem) : Prop where
  saved : Saved s₀ mS
  tbl : TblMem (scr s₀) ka kb mS
  frame : Frame [scrR s₀] s₀.mem mS

theorem tbl_of {s₀ : State} (hp : Pre s₀) {ka kb : BitVec 64} {mS : Mem} (hS : SetupMem s₀ ka kb mS)
    {s : State} (hr8 : s.gpr .r8 = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : MemInv s₀ mS s.mem) {q : Nat} (hq : q < 3) : Tbl s q (hword ka kb q) := by
  intro t ht
  have e1 : (8 * q + t) / 8 = q := by omega
  have e2 : (8 * q + t) % 8 = t := by omega
  have := hS.tbl (8 * q + t) (by omega)
  rw [e1, e2] at this
  simp only [readSrc, State.load64, ea_at, hr8, hrd, hwr]
  rw [ite_eq_left (hp.in_save (by simp only [off]; omega)), hm.readW_low hp (by simp only [off]; omega),
    this]

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (mS : Mem) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = yp s₀
  r8 : s.gpr .r8 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : MemInv s₀ mS s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (mS : Mem) (i : Nat) (s : State) : Prop extends Common s₀ mS i s where
  rdi : s.gpr .rdi = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)

/-- The registers a block changes, besides `rdi` and `rcx` at its end. -/
abbrev bigClob : List Reg := [.rax, .rdx, .rbx, .rbp, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The pointers during block `i`. -/
structure Ptrs (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = yp s₀
  r8 : s.gpr .r8 = scr s₀
  rdi : s.gpr .rdi = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem LInv.ptrs {s₀ : State} {mS : Mem} {i : Nat} {s : State} (h : LInv s₀ mS i s) : Ptrs s₀ i s :=
  ⟨h.rsi, h.r8, h.rdi, h.rcx, h.rsp, h.rd, h.wr⟩

namespace Ptrs
variable {s₀ : State} {i : Nat} {s : State} (h : Ptrs s₀ i s)
include h

theorem of_regs {s' : State} (hr : Regs bigClob s s') : Ptrs s₀ i s' :=
  ⟨(hr.1 _ (by decide)).trans h.rsi, (hr.1 _ (by decide)).trans h.r8, (hr.1 _ (by decide)).trans h.rdi,
    (hr.1 _ (by decide)).trans h.rcx, (hr.1 _ (by decide)).trans h.rsp, hr.2.1.trans h.rd,
    hr.2.2.trans h.wr⟩

variable (hp : Pre s₀)
include hp

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.rsi]; exact hp.in_y hd

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.wr, h.rsi]; exact hp.out_y hd

theorem in_s {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.r8]; exact hp.in_save hd

theorem out_s {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.wr, h.r8]; exact hp.out_save hd

theorem in_x (hi : i < nb s₀) {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.rdi]; exact hp.in_blk hi hd

/-- A load of `y` or `scratch`. -/
theorem load_y {d : Nat} (hd : d + 8 ≤ 16) :
    readSrc s (.mem (at_ .rsi d)) = some (s.mem.readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64) := by
  simp only [readSrc, State.load64, ea_at, h.in_y hp hd, ite_true]
  rw [h.rsi]

theorem load_s {d : Nat} (hd : d + 8 ≤ 256) :
    readSrc s (.mem (at_ .r8 d)) = some (s.mem.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64) := by
  simp only [readSrc, State.load64, ea_at, h.in_s hp hd, ite_true]
  rw [h.r8]

end Ptrs

/-! ## One block -/

theorem blockAt_bswap' (m : Mem) (p : Addr) :
    X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
      X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) = blockAt m p := by
  rw [ofInt_natCast, ofInt_natCast]; exact blockAt_bswap m p

/-- The memory after storing `Z` at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) (bswap64 zh)).writeW
    (p + BitVec.ofInt 64 ((8 : Nat) : Int)) (bswap64 zl)

theorem half_sep (p : Addr) :
    Mem.Sep (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 8 (p + BitVec.ofInt 64 ((8 : Nat) : Int)) 8 := by
  simp only [ofInt_natCast]
  exact Offset.sep p (by decide) (by decide) (by decide)

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) :
    blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_bswap', storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (half_sep p) (by decide), Mem.readW_writeW_self64, bswap64_bswap64,
    bswap64_bswap64]

/-- Memory outside `y` and `scratch` is as on entry. -/
theorem blockAt_frame {s₀ : State} {m : Mem} (h : Frame [yR s₀, scrR s₀] s₀.mem m) {p : Addr}
    (hd : ∀ r ∈ [yR s₀, scrR s₀], Region.Disjoint ⟨p, 16⟩ r) : blockAt m p = blockAt s₀.mem p :=
  blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem blkAddr_succ (s₀ : State) (i : Nat) : blkAddr s₀ i + 16 = blkAddr s₀ (i + 1) := by
  rw [blkAddr, blkAddr, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, Nat.mul_succ]

theorem ofNat_sub_succ {n i : Nat} (hi : i < n) :
    BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

theorem body_ok {s₀ : State} (hp : Pre s₀) {ka kb : BitVec 64} {mS : Mem}
    (hS : SetupMem s₀ ka kb mS) (hH : x * φ (ka ++ kb) = φ (H₀ s₀)) {i : Nat} (hi : i < nb s₀)
    {s : State} (hL : LInv s₀ mS i s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ mS (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ mS (i + 1) s') := by
  rw [body]
  repeat rw [WP.block_append_iff]
  have P₀ := hL.ptrs
  -- load `Y ⊕ X`
  refine WP.mono (load_ok s (P₀.in_y hp (d := 0) (by decide)) (P₀.in_y hp (d := 8) (by decide))
    (P₀.in_x hp hi (d := 0) (by decide)) (P₀.in_x hp hi (d := 8) (by decide)) (P₀.out_y hp (d := 8) (by decide))
    (P₀.out_s hp (d := 240) (by decide)))
    fun s₁ ⟨hW₁, hm₁, hr₁⟩ => ?_
  rw [P₀.rsi, P₀.rdi] at hW₁
  rw [P₀.rsi, P₀.rdi, P₀.r8] at hm₁
  generalize hyB : bswap64 (s.mem.readW (yp s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
    bswap64 (s.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) = yB at hm₁
  have P₁ := P₀.of_regs (hr₁.mono (by decide))
  have M₁ : MemInv s₀ mS s₁.mem := by
    rw [hm₁]; exact (hL.mem.write_y (by decide) _).write_slot (by decide) (by decide) _
  -- `A = Y_A · H'_A`
  refine WP.mono (product_ok (.reg W0) 0 (yv := s₁.gpr W0)
    (tbl_of hp hS P₁.r8 P₁.rd P₁.wr M₁ (by decide))
    (fun s' hk => by simp only [readSrc]; rw [hk.1 W0 (by decide)])) fun s₂ ⟨hP₂, hk₂⟩ => ?_
  have P₂ := P₁.of_regs (hk₂.regs.mono (by decide))
  -- keep `A`
  refine WP.mono (keepA_ok s₂ (P₂.out_y hp (d := 0) (by decide))) fun s₃ ⟨hW₃, hm₃, hr₃⟩ => ?_
  rw [P₂.rsi, hk₂.2.1] at hm₃
  have P₃ := P₂.of_regs (hr₃.mono (by decide))
  have M₃ : MemInv s₀ mS s₃.mem := by rw [hm₃]; exact M₁.write_y (by decide) _
  -- `B = Y_B · H'_B`
  refine WP.mono (product_ok (.mem (at_ .rsi 8)) 1 (yv := yB)
    (tbl_of hp hS P₃.r8 P₃.rd P₃.wr M₃ (by decide))
    (fun s' hk => by
      rw [hk.readSrc_mem (by decide), P₃.load_y hp (d := 8) (by decide), hm₃,
        readW_writeW_off _ _ _ (by decide) (by decide) (by decide), hm₁, hp.readW_y_s _ _ (by decide) (by decide),
        Mem.readW_writeW_self64])) fun s₄ ⟨hP₄, hk₄⟩ => ?_
  have P₄ := P₃.of_regs (hk₄.regs.mono (by decide))
  -- keep `A ⊕ B`
  refine WP.mono (keepB_ok s₄ (P₄.in_y hp (d := 0) (by decide)) (P₄.out_y hp (d := 0) (by decide))
    (P₄.out_y hp (d := 8) (by decide)) (P₄.out_s hp (d := 248) (by decide))) fun s₅ ⟨hm₅, hr₅⟩ => ?_
  have ha : s₃.mem.readW (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 = s₂.gpr PL := by
    rw [hm₃, Mem.readW_writeW_self64]
  rw [P₄.rsi, P₄.r8, hk₄.2.1, ha] at hm₅
  have P₅ := P₄.of_regs (hr₅.mono (by decide))
  have M₅ : MemInv s₀ mS s₅.mem := by
    rw [hm₅]; exact ((M₃.write_y (by decide) _).write_y (by decide) _).write_slot (by decide) (by decide) _
  -- `M = (Y_A ⊕ Y_B) · (H'_A ⊕ H'_B)`
  refine WP.mono (product_ok (.mem (at_ .r8 slotM)) 2 (yv := yB ^^^ s₁.gpr W0)
    (tbl_of hp hS P₅.r8 P₅.rd P₅.wr M₅ (by decide))
    (fun s' hk => by
      rw [hk.readSrc_mem (by decide), slotM, P₅.load_s hp (d := 240) (by decide), hm₅,
        readW_writeW_off _ _ _ (by decide) (by decide) (by decide), hp.readW_s_y _ _ (by decide) (by decide),
        hp.readW_s_y _ _ (by decide) (by decide), hm₃, hp.readW_s_y _ _ (by decide) (by decide),
        hm₁, Mem.readW_writeW_self64, hW₁])) fun s₆ ⟨hP₆, hk₆⟩ => ?_
  have P₆ := P₅.of_regs (hk₆.regs.mono (by decide))
  -- `W₁, W₂, W₃`
  refine WP.mono (keepM_ok s₆ (P₆.in_y hp (d := 0) (by decide)) (P₆.in_y hp (d := 8) (by decide))
    (P₆.in_s hp (d := 248) (by decide)))
    fun s₇ ⟨hAL₇, hAH₇, hPL₇, hk₇⟩ => ?_
  rw [P₆.rsi, hk₆.2.1, hm₅, hp.readW_y_s _ _ (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64] at hAL₇
  rw [P₆.rsi, hk₆.2.1, hm₅, hp.readW_y_s _ _ (by decide) (by decide), Mem.readW_writeW_self64] at hAH₇
  rw [P₆.r8, hk₆.2.1, hm₅, Mem.readW_writeW_self64] at hPL₇
  -- the reduction
  refine WP.mono (fold_ok PL AL AH (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s₇) fun s₈ ⟨hAL₈, hAH₈, hk₈⟩ => ?_
  refine WP.mono (fold_ok AH W0 AL (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s₈) fun s₉ ⟨hW₉, hAL₉, hk₉⟩ => ?_
  have P₉ := P₆.of_regs (((hk₇.regs.mono (c' := bigClob) (by decide)).trans
    (hk₈.regs.mono (by decide))).trans (hk₉.regs.mono (by decide)))
  -- store `Y`
  refine WP.mono (store_ok s₉ (P₉.out_y hp (d := 0) (by decide)) (P₉.out_y hp (d := 8) (by decide)))
    fun s₁₀ ⟨hm₁₀, hrdi₁₀, hrcx₁₀, hzf₁₀, hr₁₀⟩ => ?_
  rw [P₉.rsi] at hm₁₀
  -- the memory after the block
  have hmem₉ : s₉.mem = s₅.mem := hk₉.2.1.trans (hk₈.2.1.trans (hk₇.2.1.trans hk₆.2.1))
  have M₁₀ : MemInv s₀ mS s₁₀.mem := by
    rw [hm₁₀, hmem₉]; exact (M₅.write_y (by decide) _).write_y (by decide) _
  -- the new `Y`
  have hW0₈ : s₈.gpr W0 = s₂.gpr PH := by
    rw [hk₈.1 W0 (by decide), hk₇.1 W0 (by decide), hk₆.1 W0 (by decide), hr₅.1 W0 (by decide),
      hk₄.1 W0 (by decide), hW₃]
  have hW0₄ : s₄.gpr W0 = s₂.gpr PH := by rw [hk₄.1 W0 (by decide), hW₃]
  rw [hW0₄] at hAL₇
  have hy : blockAt s₁₀.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hX : blockAt s.mem (yp s₀) ^^^ blockAt s.mem (blkAddr s₀ i) = s₁.gpr W0 ++ yB := by
      rw [← blockAt_bswap', ← blockAt_bswap', BitVec.xor_append, ← hW₁, hyB]
    have hA' : s₂.gpr PH ++ s₂.gpr PL = prodVal ka (s₁.gpr W0) := hP₂
    have hB' : s₄.gpr PH ++ s₄.gpr PL = prodVal kb yB := hP₄
    have hM' : s₆.gpr PH ++ s₆.gpr PL = prodVal (ka ^^^ kb) (s₁.gpr W0 ^^^ yB) := by
      rw [hP₆, BitVec.xor_comm yB]; rfl
    rw [ghashFrom_blocksAt_succ, ← hL.y,
      ← blockAt_frame (p := blkAddr s₀ i) hL.mem.f1 (by simpa using
        ⟨(hp.y_d.symm.sub_left (hp.blk_sub hi)), hp.d_scr.sub_left (hp.blk_sub hi)⟩),
      hX, ← reduce_eq_mul hH hA' hB' hM', hm₁₀]
    show blockAt (storeMem s₉.mem (yp s₀) (s₉.gpr W0) (s₉.gpr AL)) (yp s₀) = _
    rw [blockAt_storeMem, hW₉, hAL₉, hAL₈, hAH₈, hW0₈, hAL₇, hAH₇, hPL₇]
    rfl
  have hk : ∀ r ∈ [Reg.rsi, .r8, .rsp], s₁₀.gpr r = s₉.gpr r := fun r hr => hr₁₀.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)
  have hrcx : s₉.gpr .rcx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [P₉.rcx]; exact ofNat_sub_succ hi
  have hcommon : Common s₀ mS (i + 1) s₁₀ :=
    ⟨(hk .rsi (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans P₉.rsi, (hk .r8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true])).trans P₉.r8, (hk .rsp (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])).trans P₉.rsp,
      hr₁₀.2.1.trans P₉.rd, hr₁₀.2.2.trans P₉.wr, M₁₀, hy⟩
  have hev : eval .ne s₁₀ = some (!(BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hzf₁₀, hrcx, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨by rw [hev]; decide, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with rdi := ?_, rcx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrdi₁₀, P₉.rdi, blkAddr_succ]
    · rw [hrcx₁₀, hrcx]

/-! ## The set-up -/

theorem save_eq : save = [
    .store (at_ .r8 0) .rbx, .store (at_ .r8 8) .rbp, .store (at_ .r8 16) .r12,
    .store (at_ .r8 24) .r13, .store (at_ .r8 32) .r14, .store (at_ .r8 40) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .r8 0)), .mov .rbp (.mem (at_ .r8 8)), .mov .r12 (.mem (at_ .r8 16)),
    .mov .r13 (.mem (at_ .r8 24)), .mov .r14 (.mem (at_ .r8 32)), .mov .r15 (.mem (at_ .r8 40))] := rfl

/-- The memory after saving the registers. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) (s₀.gpr .r15)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := hp.out_save (d := 0) (by decide); have o1 := hp.out_save (d := 8) (by decide)
  have o2 := hp.out_save (d := 16) (by decide); have o3 := hp.out_save (d := 24) (by decide)
  have o4 := hp.out_save (d := 32) (by decide); have o5 := hp.out_save (d := 40) (by decide)
  apply WP.of_runBlock
  rw [save_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_off]

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 →
      (scrR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
    (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 32 (by decide)) |>.writeW (List.mem_singleton_self _) _
    (c 40 (by decide))

theorem Saved.write {s₀ : State} {m : Mem} (h : Saved s₀ m) {e : Nat} (he : 48 ≤ e) (he' : e < 2 ^ 32)
    (v : BitVec 64) : Saved s₀ (m.writeW (scr s₀ + BitVec.ofInt 64 (e : Int)) v) := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
  exact ⟨(readW_writeW_off _ _ _ (d := 0) (by decide) he' (by omega)).trans g0,
    (readW_writeW_off _ _ _ (d := 8) (by decide) he' (by omega)).trans g1,
    (readW_writeW_off _ _ _ (d := 16) (by decide) he' (by omega)).trans g2,
    (readW_writeW_off _ _ _ (d := 24) (by decide) he' (by omega)).trans g3,
    (readW_writeW_off _ _ _ (d := 32) (by decide) he' (by omega)).trans g4,
    (readW_writeW_off _ _ _ (d := 40) (by decide) he' (by omega)).trans g5⟩

theorem tbl_word {s : State} {ka kb : BitVec 64} (hAL : s.gpr AL = ka) (hAH : s.gpr AH = kb)
    (hPH : s.gpr PH = ka ^^^ kb) (q : Nat) : s.gpr (tblReg q) = hword ka kb q := by
  rcases q with _ | _ | q
  · exact hAL
  · exact hAH
  · exact hPH

/-- While the tables are written: `k` parts done. -/
def EInv (s₀ s₂ : State) (k : Nat) (s : State) : Prop :=
  Regs [.rax] s₂ s ∧ Frame [scrR s₀] s₀.mem s.mem ∧ Saved s₀ s.mem ∧
  ∀ u < k, s.mem.readW (scr s₀ + BitVec.ofInt 64 ((off u : Nat) : Int)) 64 =
    part (hword (s₂.gpr AL) (s₂.gpr AH) (u / 8)) (u % 8)

theorem entry_step {s₀ s₂ : State} (hp : Pre s₀) (hr8 : s₂.gpr .r8 = scr s₀) (hwr : s₂.wr = s₀.wr)
    (hPH : s₂.gpr PH = s₂.gpr AL ^^^ s₂.gpr AH) (k : Nat) (s : State) (hk : k < 24)
    (hI : EInv s₀ s₂ k s) : WP isa (.block (entry k)) s (EInv s₀ s₂ (k + 1)) := by
  obtain ⟨hr, hf, hsv, ht⟩ := hI
  have hr8' : s.gpr .r8 = scr s₀ := (hr.1 _ (by decide)).trans hr8
  have ho : off k + 8 ≤ 240 := by simp only [off]; omega
  refine WP.mono (entry_ok k s (by rw [hr.2.2, hwr, hr8']; exact hp.out_save (by omega)))
    fun s' ⟨hm, hr'⟩ => ?_
  rw [hr8', hr.1 _ (by simpa using tblReg_ne (k / 8)), tbl_word rfl rfl hPH] at hm
  refine ⟨hr.trans hr', ?_, ?_, fun u hu => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
  · rw [hm]; exact hsv.write (by simp only [off]; omega) (by omega) _
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
    · rw [readW_writeW_off _ _ _ (by simp only [off]; omega) (by omega) (by simp only [off]; omega)]
      exact ht u hu
    · rw [Mem.readW_writeW_self64, part, show u % 8 % 2 = u % 2 by omega]

/-- The registers the set-up changes. -/
abbrev setupClob : List Reg := [AL, AH, .rax, PL, PH, .rdi]

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ => ∃ ka kb, x * φ (ka ++ kb) = φ (H₀ s₀) ∧
      SetupMem s₀ ka kb s₁.mem ∧ s₁.zf = some (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) ∧
      s₁.gpr .rdi = dp s₀ ∧ Regs setupClob s₀ s₁ := by
  rw [setup]
  repeat rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  have hh : ∀ d : Nat, d + 8 ≤ 16 → s₁.mem.readW (s₁.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64 =
      s₀.mem.readW (hA s₀ + BitVec.ofInt 64 (d : Int)) 64 := fun d hd => by
    rw [hg, hm]
    exact saveMem_frame.readW (contains_offset' (base := hA s₀) hd (by omega))
      (by simpa using hp.h_scr) (by decide)
  refine WP.mono (hInv_ok s₁ (by rw [hrd, hwr, hg]; exact hp.in_h (by decide))
    (by rw [hrd, hwr, hg]; exact hp.in_h (by decide))) fun s₂ ⟨hK, hPH, hk₂⟩ => ?_
  rw [hh 0 (by decide), hh 8 (by decide), blockAt_bswap'] at hK
  have hH : x * φ (s₂.gpr AL ++ s₂.gpr AH) = φ (H₀ s₀) := by rw [hK]; exact x_φ_hInv _
  have hr8₂ : s₂.gpr .r8 = scr s₀ := by rw [hk₂.1 _ (by decide), hg]
  have hwr₂ : s₂.wr = s₀.wr := hk₂.2.2.2.trans hwr
  refine WP.mono (wp_range_flatMap (EInv s₀ s₂) (entry_step hp hr8₂ hwr₂ hPH) 24 (Nat.le_refl _) s₂
    ⟨⟨fun _ _ => rfl, rfl, rfl⟩, by rw [hk₂.2.1, hm]; exact saveMem_frame,
      by rw [hk₂.2.1, hm]; exact saveMem_saved, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s₃ ⟨hr₃, hf₃, hsv₃, ht₃⟩ => ?_
  refine WP.mono (tail_ok s₃) fun s₄ ⟨hrdi, hzf, hk₄⟩ => ?_
  have hr : Regs setupClob s₀ s₃ :=
    ((show Regs setupClob s₀ s₁ from ⟨fun r _ => by rw [hg], hrd, hwr⟩).trans
      (hk₂.regs.mono (by decide))).trans (hr₃.mono (by decide))
  refine ⟨s₂.gpr AL, s₂.gpr AH, hH, ⟨?_, ?_, ?_⟩, ?_, ?_, hr.trans (hk₄.regs.mono (by decide))⟩
  · rw [hk₄.2.1]; exact hsv₃
  · rw [hk₄.2.1]; exact ht₃
  · rw [hk₄.2.1]; exact hf₃
  · rw [hzf, hr.1 _ (by decide)]
  · rw [hrdi, hr.1 _ (by decide)]

/-! ## The end -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {mS : Mem} (hsv : Saved s₀ mS) {s : State}
    (hc : Common s₀ mS (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Gcm.ghashX86_64.post s₀ s' := by
  have i0 := hp.in_save (d := 0) (by decide); have i1 := hp.in_save (d := 8) (by decide)
  have i2 := hp.in_save (d := 16) (by decide); have i3 := hp.in_save (d := 24) (by decide)
  have i4 := hp.in_save (d := 32) (by decide); have i5 := hp.in_save (d := 40) (by decide)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hsv
  rw [← hc.mem.readW_low hp (by decide)] at g0 g1 g2 g3 g4 g5
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.mem.f1.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_y, hp.ret_scr⟩) (by decide)
  have hrsp := hc.rsp
  have hy := hc.y
  have hr8 := hc.r8
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr8, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · exact hret
  · exact hy

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Gcm.ghashX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨ka, kb, hH, hS, hzf, hrdi, hr⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ s₁.mem (nb s₀)) ?_ fun s₂ hc => restore_ok hp hS.saved hc)
  have hc₀ : Common s₀ s₁.mem 0 s₁ := by
    refine ⟨hr.1 _ (by decide), hr.1 _ (by decide), hr.1 _ (by decide), hr.2.1, hr.2.2,
      ⟨hS.frame.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp only [hr, List.mem_cons, Region.mk.injEq, Nat.reduceEqDiff, and_false, List.not_mem_nil, or_false, or_true], Frame.refl _ _⟩, ?_⟩
    rw [ghashFrom_blocksAt_zero]
    exact blockAt_congr fun _ hk =>
      hS.frame.bytes (R := yR s₀) (by simpa using hp.y_scr) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  refine WP.ite (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) (by simp only [eval, hzf, BitVec.and_self, BitVec.ofNat_eq_ofNat]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, BitVec.ofNat_eq_ofNat, beq_iff_eq] at h; simp only [nb, h, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ s₁.mem i s
    have hstep : ∀ m s, Inv m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ s₁.mem (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hS hH hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ s₁.mem 0 s₁ :=
      { hc₀ with
        rdi := by rw [hrdi]; simp only [blkAddr, mul_zero, BitVec.add_zero]
        rcx := by rw [hr.1 _ (by decide)]; simp only [nb, tsub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86_64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86_64.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86_64.pre Proof.Gcm.ghashX86_64.pub
    Impl.Gcm.X86_64.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem ghash_verified :
    Verified X86_64.target Impl.Gcm.X86_64.ghash (Spec.Gcm.ghashContract X86_64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Gcm.X86_64.satState] using Proof.Gcm.X86_64.satState)

end VG.Proof.Gcm.X86_64

end
