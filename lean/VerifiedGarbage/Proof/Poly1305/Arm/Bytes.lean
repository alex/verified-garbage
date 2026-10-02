import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.TCB.Arm.Target

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Common`.
section

section

/-!
# Poly1305 on 32-bit ARM: the arithmetic in radix `2¹³`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/Arm.lean`), as natural numbers: a number is ten limbs
`f 0, …, f 9` of 13 bits (`val`), possibly larger; the columns of a product
modulo `p` (`col`); the carries (`carryN`); the limbs of four 32-bit words
(`mlimb`) and back (`toWords`); and the final reduction.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG.Spec.Poly1305 (P)

/-! ## `if` -/

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp only [h, ↓reduceIte]

/-! ## Limbs -/

/-- The number whose limbs are `f 0, …, f 9`. -/
def val (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 13 * f 1 + 2 ^ 26 * f 2 + 2 ^ 39 * f 3 + 2 ^ 52 * f 4 + 2 ^ 65 * f 5 + 2 ^ 78 * f 6 +
    2 ^ 91 * f 7 + 2 ^ 104 * f 8 + 2 ^ 117 * f 9

theorem val_congr {f g : Nat → Nat} (h : ∀ k < 10, f k = g k) : val f = val g := by
  simp only [val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

/-- `Σ_{j < n} f j`. -/
def rsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rsum f n + f n

theorem rsum_le {f g : Nat → Nat} (h : ∀ j, f j ≤ g j) : ∀ n, rsum f n ≤ rsum g n
  | 0 => (Nat.le_refl _)
  | n + 1 => Nat.add_le_add (rsum_le h n) (h n)

theorem rsum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : rsum f m ≤ rsum f n := by
  induction n with
  | zero => exact Nat.le_of_eq (congrArg (rsum f) (Nat.le_zero.mp h))
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega_using [h'])) (Nat.le_add_right _ _)
    · exact Nat.le_of_eq (congrArg (rsum f) (by omega_using [h, h']))

theorem rsum_const (c : Nat) : ∀ n, rsum (fun _ => c) n = n * c
  | 0 => by simp only [rsum, Nat.zero_mul]
  | n + 1 => by rw [rsum, rsum_const c n, Nat.succ_mul]

/-! ## The columns of a product -/

/-- The coefficient of `h j` in column `k` of `h r` modulo `p`. -/
def coef (r : Nat → Nat) (k j : Nat) : Nat := if j ≤ k then r (k - j) else 5 * r (k + 10 - j)

/-- Column `k` after the rows `j' < j` and, of row `j`, the products of `r i`
for `i < n`, which are added to column `(i + j) mod 10`. -/
def psum (h r : Nat → Nat) (j n k : Nat) : Nat :=
  rsum (fun j' => h j' * coef r k j') j + if (k + 10 - j) % 10 < n then h j * coef r k j else 0

/-- Column `k` of `h r` modulo `p`. -/
def col (h r : Nat → Nat) (k : Nat) : Nat := rsum (fun j => h j * coef r k j) 10

theorem psum_zero (h r : Nat → Nat) (k : Nat) : psum h r 0 0 k = 0 := by
  simp only [psum, rsum, Nat.sub_zero, Nat.add_mod_right, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero]

theorem psum_row (h r : Nat → Nat) (j k : Nat) :
    psum h r j 10 k = psum h r (j + 1) 0 k := by
  simp only [psum, rsum, Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.mod_lt _ (by decide)))]

theorem psum_ten (h r : Nat → Nat) (k : Nat) : psum h r 10 0 k = col h r k := by
  simp only [psum, Nat.add_sub_cancel, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero, col]

/-- The product `r i` of row `j`, for `i < 10`, is `h j * r i`, or `5 * h j * r i`
once `i + j ≥ 10`. -/
theorem psum_step (h r : Nat → Nat) {j i k : Nat} (hj : j < 10) (hi : i < 10) (hk : k < 10) :
    psum h r j (i + 1) k =
      if k = (i + j) % 10 then psum h r j i k +
        (if i + j < 10 then h j else 5 * h j) * r i
      else psum h r j i k := by
  by_cases e : k = (i + j) % 10
  · subst e
    simp only [psum, coef, ite_true]
    have e1 : ((i + j) % 10 + 10 - j) % 10 = i := by omega_using [hj, hi, hk]
    rw [e1, ite_eq_left_of_eq_true _ _ (eq_true (show i < i + 1 by omega_using [])),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < i by omega_using []))]
    by_cases hij : i + j < 10
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true (show j ≤ (i + j) % 10 by omega_using [hj, hi, hk, e1, hij])),
        show (i + j) % 10 - j = i by omega_using [hj, hi, hk, e1, hij]]; omega_using []
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j ≤ (i + j) % 10 by omega_using [hj, hi, hk, e1, hij])),
        show (i + j) % 10 + 10 - j = i by omega_using [hj, hi, hk, e1, hij], Nat.mul_left_comm, Nat.mul_assoc]; omega_using []
  · have e' : ((k + 10 - j) % 10 < i + 1) = ((k + 10 - j) % 10 < i) := by
      apply propext; omega_using [hj, hk, e]
    simp only [psum, e', e, ite_false]

theorem psum_le_col (h r : Nat → Nat) {j n k : Nat} (hj : j < 10) :
    psum h r j n k ≤ col h r k := by
  simp only [psum, col]
  have : rsum (fun j' => h j' * coef r k j') j + h j * coef r k j ≤
      rsum (fun j' => h j' * coef r k j') 10 :=
    rsum_mono (fun j' => h j' * coef r k j') (show j + 1 ≤ 10 by omega_using [hj])
  split <;> omega_using [this]

theorem rsum_le_of_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j ≤ g j) → rsum f n ≤ rsum g n
  | 0, _ => (Nat.le_refl _)
  | n + 1, h => Nat.add_le_add (rsum_le_of_lt n fun j hj => h j (by omega_using [hj])) (h n (by omega_using []))

/-- A bound on every column. -/
theorem col_le {h r : Nat → Nat} {H R : Nat} (hh : ∀ j < 10, h j ≤ H) (hr : ∀ i < 10, r i ≤ R)
    {k : Nat} (hk : k < 10) : col h r k ≤ 10 * (H * (5 * R)) := by
  have : ∀ j < 10, h j * coef r k j ≤ H * (5 * R) := fun j hj => by
    apply Nat.mul_le_mul (hh j hj)
    simp only [coef]; split
    · have := hr (k - j) (by omega_using [hk, hj]); omega_using [this]
    · have := hr (k + 10 - j) (by omega); omega
  have := rsum_le_of_lt 10 this
  rw [rsum_const] at this
  exact this

theorem P_eq : P = 2 ^ 130 - 5 := rfl

/-! ## The columns of a product, as a number -/

theorem rsum_add (f g : Nat → Nat) : ∀ n, rsum (fun j => f j + g j) n = rsum f n + rsum g n
  | 0 => rfl
  | n + 1 => by simp only [rsum, rsum_add f g n]; omega_using []

theorem rsum_mul (c : Nat) (f : Nat → Nat) : ∀ n, c * rsum f n = rsum (fun j => c * f j) n
  | 0 => rfl
  | n + 1 => by rw [rsum, rsum, Nat.mul_add, rsum_mul c f n]

theorem rsum_congr {f g : Nat → Nat} (h : ∀ j, f j = g j) : ∀ n, rsum f n = rsum g n
  | 0 => rfl
  | n + 1 => by rw [rsum, rsum, rsum_congr h n, h n]

theorem rsum_congr_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j = g j) → rsum f n = rsum g n
  | 0, _ => rfl
  | n + 1, h => by rw [rsum, rsum, rsum_congr_lt n (fun j hj => h j (by omega_using [hj])), h n (by omega_using [])]

theorem modP_of_eq {X V K : Nat} (h : X + 5 * K = V + 2 ^ 130 * K) : V % P = X % P := by
  have : X = V + P * K := by rw [P_eq]; omega_using [h]
  rw [this, Nat.add_mul_mod_self_left]

theorem rsum_comm (f : Nat → Nat → Nat) (m : Nat) : ∀ n,
    rsum (fun k => rsum (fun j => f k j) m) n = rsum (fun j => rsum (fun k => f k j) n) m
  | 0 => by
    induction m with
    | zero => rfl
    | succ m ih => simp only [rsum] at ih ⊢; omega_using [ih]
  | n + 1 => by
    rw [rsum, rsum_comm f m n, ← rsum_add]; rfl

theorem val_eq (f : Nat → Nat) : val f = rsum (fun k => 2 ^ (13 * k) * f k) 10 := by
  simp only [val, rsum]; omega_using []

/-- The terms of row `j` of `h r` that wrap around: `2¹³⁰ ≡ 5`. -/
def wrap (r : Nat → Nat) (j : Nat) : Nat := rsum (fun i => if 10 ≤ i + j then 2 ^ (13 * (i + j - 10)) * r i else 0) 10

theorem row_wrap (r : Nat → Nat) {j : Nat} (hj : j < 10) :
    2 ^ (13 * j) * val r + 5 * wrap r j = rsum (fun k => 2 ^ (13 * k) * coef r k j) 10 + 2 ^ 130 * wrap r j := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  all_goals
    simp (config := {decide := true}) only [val, wrap, rsum, coef, ite_true, ite_false, Nat.reduceSub,
      Nat.reduceAdd, Nat.reduceMul, Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.mul_add,
      ← Nat.mul_assoc, Nat.reducePow, Nat.mul_one, Nat.one_mul] <;>
    ac_rfl

/-- The columns of `h r`, as a number, are `h r` modulo `p`. -/
theorem val_col (h r : Nat → Nat) : val (col h r) % P = val h * val r % P := by
  have e1 : val (col h r) = rsum (fun j => h j * rsum (fun k => 2 ^ (13 * k) * coef r k j) 10) 10 := by
    rw [val_eq, rsum_congr (fun k => by rw [col, rsum_mul]) 10, rsum_comm]
    refine rsum_congr (fun j => ?_) 10
    rw [rsum_mul]
    exact rsum_congr (fun k => Nat.mul_left_comm _ _ _) 10
  have e2 : val h * val r = rsum (fun j => h j * (2 ^ (13 * j) * val r)) 10 := by
    rw [val_eq h, Nat.mul_comm, rsum_mul]
    refine rsum_congr (fun j => ?_) 10
    rw [Nat.mul_comm (val r), Nat.mul_left_comm]
    exact Nat.mul_assoc _ _ _
  have key : val h * val r + 5 * rsum (fun j => h j * wrap r j) 10 =
      val (col h r) + 2 ^ 130 * rsum (fun j => h j * wrap r j) 10 := by
    rw [e1, e2, rsum_mul, rsum_mul, ← rsum_add, ← rsum_add]
    refine rsum_congr_lt 10 (fun j hj => ?_)
    have e := congrArg (h j * ·) (row_wrap r hj)
    simp only [Nat.mul_add] at e
    rw [Nat.mul_left_comm (h j) 5, Nat.mul_left_comm (h j) (2 ^ 130)] at e
    exact e
  exact modP_of_eq key

/-! ## Carrying -/

/-- Column `k`'s bits from 13 up moved to column `k + 1`. -/
def cstep (f : Nat → Nat) (k : Nat) : Nat → Nat :=
  fun j => if j = k then f k % 2 ^ 13 else if j = k + 1 then f (k + 1) + f k / 2 ^ 13 else f j

theorem val_cstep (f : Nat → Nat) {k : Nat} (hk : k < 9) : val (cstep f k) = val f := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp [val, cstep]; omega_using []

/-- The carries from columns `a`, …, `a + n - 1`, in order. -/
def carryN (f : Nat → Nat) (a : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => cstep (carryN f a n) (n + a)

theorem val_carryN (f : Nat → Nat) (a : Nat) : ∀ n, n + a ≤ 9 → val (carryN f a n) = val f
  | 0, _ => rfl
  | n + 1, h => by rw [carryN, val_cstep _ (by omega_using [h]), val_carryN f a n (by omega_using [h])]

theorem carryN_above (f : Nat → Nat) (a : Nat) : ∀ n j, n + a < j → carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [carryN, cstep, show j ≠ n + a by omega_using [h], show j ≠ n + a + 1 by omega_using [h], ite_false]
    exact carryN_above f a n j (by omega_using [h])

theorem carryN_below (f : Nat → Nat) (a : Nat) : ∀ n j, j < a → carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [carryN, cstep, show j ≠ n + a by omega_using [h], show j ≠ n + a + 1 by omega_using [h], ite_false]
    exact carryN_below f a n j h

theorem carryN_lt (f : Nat → Nat) (a : Nat) : ∀ n j, a ≤ j → j < n + a → carryN f a n j < 2 ^ 13
  | 0, _, h₁, h₂ => by omega_using [h₁, h₂]
  | n + 1, j, h₁, h₂ => by
    simp only [carryN, cstep]
    by_cases e : j = n + a
    · simp only [e, ite_true]; exact Nat.mod_lt _ (by decide)
    · simp only [e, show j ≠ n + a + 1 by omega_using [h₂], ite_false]
      exact carryN_lt f a n j h₁ (by omega_using [h₂, e])

/-- The column being carried into, if every column is below `2³² - 2¹⁹`. -/
theorem carryN_top (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    ∀ n, n + a ≤ 9 → carryN f a n (n + a) < 2 ^ 32
  | 0, h => by have := hf a (by omega_using [h]); simp only [carryN, Nat.zero_add]; omega_using [this]
  | n + 1, h => by
    have ih := carryN_top f a hf n (by omega_using [h])
    have e : n + 1 + a = n + a + 1 := by omega_using []
    simp only [carryN, cstep, e, show n + a + 1 ≠ n + a by omega_using [], ite_false, ite_true]
    rw [carryN_above f a n _ (by omega_using [])]
    have := hf (n + a + 1) (by omega_using [h])
    have : carryN f a n (n + a) / 2 ^ 13 < 2 ^ 19 := by omega_using [ih]
    omega

/-- The carry step's sum does not overflow. -/
theorem carryN_step_lt (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) (n : Nat)
    (hn : n + a < 9) :
    carryN f a n (n + a + 1) + carryN f a n (n + a) / 2 ^ 13 < 2 ^ 32 := by
  have := carryN_top f a hf n (by omega_using [hn])
  rw [carryN_above f a n _ (by omega_using [])]
  have := hf (n + a + 1) (by omega_using [hn])
  omega

/-- After carrying from columns `0, …, 8`, and then adding column 9's bits from 13 up, times 5,
to column 0 and carrying it once more: the result is congruent to the columns modulo `p`
(`p c` less), and its limbs are below `2¹³` but the second, which is below `2¹³ + 2⁹`. -/
def fold (f : Nat → Nat) : Nat → Nat :=
  let F := carryN f 0 9
  cstep (fun j => if j = 0 then F 0 + 5 * (F 9 / 2 ^ 13) else if j = 9 then F 9 % 2 ^ 13 else F j) 0

theorem fold_0 (f : Nat → Nat) :
    fold f 0 = (carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)) % 2 ^ 13 := by
  simp only [fold, Nat.reducePow, cstep, ↓reduceIte]

theorem fold_1 (f : Nat → Nat) :
    fold f 1 = carryN f 0 9 1 + (carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)) / 2 ^ 13 := by
  simp [fold, cstep]

theorem fold_9 (f : Nat → Nat) : fold f 9 = carryN f 0 9 9 % 2 ^ 13 := by
  simp only [fold, Nat.reducePow, cstep, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.reduceEqDiff]

theorem fold_mid (f : Nat → Nat) {j : Nat} (h1 : 2 ≤ j) (h2 : j < 9) : fold f j = carryN f 0 9 j := by
  simp only [fold, cstep]
  simp only [show j ≠ 0 by omega_using [h1, h2], show j ≠ 1 by omega_using [h1, h2], show j ≠ 9 by omega_using [h1, h2], show 0 + 1 = 1 from rfl,
    ite_false]

theorem fold_facts (f : Nat → Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    val (fold f) % P = val f % P ∧ val (fold f) < 2 ^ 130 + 2 ^ 22 ∧ fold f 0 < 2 ^ 13 ∧
      fold f 1 < 2 ^ 13 + 2 ^ 9 ∧ ∀ j, 2 ≤ j → j < 10 → fold f j < 2 ^ 13 := by
  have hv := val_carryN f 0 9 (by decide)
  have ht := carryN_top f 0 hf 9 (by decide)
  have hl : ∀ j < 9, carryN f 0 9 j < 2 ^ 13 := fun j hj => carryN_lt f 0 9 j (by omega_using [hj]) (by omega_using [hj])
  simp only [Nat.add_zero] at ht
  have e : ∀ j, fold f j = cstep (fun j => if j = 0 then carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)
      else if j = 9 then carryN f 0 9 9 % 2 ^ 13 else carryN f 0 9 j) 0 j := fun j => rfl
  generalize carryN f 0 9 = F at hv ht hl e
  have f0 : fold f 0 = (F 0 + 5 * (F 9 / 2 ^ 13)) % 2 ^ 13 := by rw [e]; simp only [cstep, ↓reduceIte, Nat.reducePow]
  have f1 : fold f 1 = F 1 + (F 0 + 5 * (F 9 / 2 ^ 13)) / 2 ^ 13 := by rw [e]; simp [cstep]
  have f9 : fold f 9 = F 9 % 2 ^ 13 := by rw [e]; simp only [cstep, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.reduceEqDiff, Nat.reducePow]
  have fj : ∀ j, 2 ≤ j → j < 9 → fold f j = F j := by
    intro j h1 h2
    rw [e]; simp only [cstep]
    simp only [show j ≠ 0 by omega_using [h1, h2], show j ≠ 1 by omega_using [h1, h2], show j ≠ 9 by omega_using [h1, h2], show 0 + 1 = 1 from rfl,
      ite_false]
  have l0 := hl 0 (by decide); have l1 := hl 1 (by decide)
  have key : val (fold f) + P * (F 9 / 2 ^ 13) = val F := by
    simp only [val, f0, f1, f9, fj 2 (by decide) (by decide), fj 3 (by decide) (by decide),
      fj 4 (by decide) (by decide), fj 5 (by decide) (by decide), fj 6 (by decide) (by decide),
      fj 7 (by decide) (by decide), fj 8 (by decide) (by decide), P_eq]
    omega_using []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hv, ← key, Nat.add_mul_mod_self_left]
  · have l2 := hl 2 (by decide); have l3 := hl 3 (by decide); have l4 := hl 4 (by decide)
    have l5 := hl 5 (by decide); have l6 := hl 6 (by decide); have l7 := hl 7 (by decide)
    have l8 := hl 8 (by decide)
    simp only [val, f0, f1, f9, fj 2 (by decide) (by decide), fj 3 (by decide) (by decide),
      fj 4 (by decide) (by decide), fj 5 (by decide) (by decide), fj 6 (by decide) (by decide),
      fj 7 (by decide) (by decide), fj 8 (by decide) (by decide)]
    omega_using [ht, f9, l0, l1, l2, l3, l4, l5, l6, l7, l8]
  · rw [f0]; exact Nat.mod_lt _ (by decide)
  · rw [f1]; omega_using [ht, f0, f1, f9, l0, l1]
  · intro j h2 h10
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [fj j h2 h]; exact hl j h
    · rw [show j = 9 by omega_using [h2, h10, h], f9]; exact Nat.mod_lt _ (by decide)

/-! ## The limbs of four words -/

/-- Limb `k` of `w0 + 2³² w1 + 2⁶⁴ w2 + 2⁹⁶ w3`, as the code computes it: the
sum of the pieces of the words (`Impl.Poly1305.Arm.pieces`). -/
def mlimb (w0 w1 w2 w3 : Nat) : Nat → Nat
  | 0 => w0 % 2 ^ 13
  | 1 => w0 % 2 ^ 26 / 2 ^ 13
  | 2 => w0 / 2 ^ 26 + w1 % 2 ^ 7 * 2 ^ 6
  | 3 => w1 % 2 ^ 20 / 2 ^ 7
  | 4 => w1 / 2 ^ 20 + w2 % 2 * 2 ^ 12
  | 5 => w2 % 2 ^ 14 / 2
  | 6 => w2 % 2 ^ 27 / 2 ^ 14
  | 7 => w2 / 2 ^ 27 + w3 % 2 ^ 8 * 2 ^ 5
  | 8 => w3 % 2 ^ 21 / 2 ^ 8
  | _ => w3 / 2 ^ 21

theorem mlimb_lt {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) (k : Nat) : mlimb w0 w1 w2 w3 k < 2 ^ 13 := by
  unfold mlimb
  split <;> omega_using [h1, h2, h3, h0]

theorem val_mlimb {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) :
    val (mlimb w0 w1 w2 w3) = w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 := by
  have e0 : w0 = w0 % 2 ^ 13 + 2 ^ 13 * (w0 % 2 ^ 26 / 2 ^ 13) + 2 ^ 26 * (w0 / 2 ^ 26) := by omega_using []
  have e1 : w1 = w1 % 2 ^ 7 + 2 ^ 7 * (w1 % 2 ^ 20 / 2 ^ 7) + 2 ^ 20 * (w1 / 2 ^ 20) := by omega_using []
  have e2 : w2 = w2 % 2 + 2 * (w2 % 2 ^ 14 / 2) + 2 ^ 14 * (w2 % 2 ^ 27 / 2 ^ 14) +
    2 ^ 27 * (w2 / 2 ^ 27) := by omega_using []
  have e3 : w3 = w3 % 2 ^ 8 + 2 ^ 8 * (w3 % 2 ^ 21 / 2 ^ 8) + 2 ^ 21 * (w3 / 2 ^ 21) := by omega_using []
  simp only [val, mlimb]
  generalize w0 % 2 ^ 13 = a0, w0 % 2 ^ 26 / 2 ^ 13 = a1, w0 / 2 ^ 26 = a2 at *
  generalize w1 % 2 ^ 7 = b0, w1 % 2 ^ 20 / 2 ^ 7 = b1, w1 / 2 ^ 20 = b2 at *
  generalize w2 % 2 = c0, w2 % 2 ^ 14 / 2 = c1, w2 % 2 ^ 27 / 2 ^ 14 = c2, w2 / 2 ^ 27 = c3 at *
  generalize w3 % 2 ^ 8 = d0, w3 % 2 ^ 21 / 2 ^ 8 = d1, w3 / 2 ^ 21 = d2 at *
  subst e0 e1 e2 e3
  omega_using []

/-! ## Words of limbs -/

theorem val_toWords {u : Nat → Nat} (h : ∀ k < 9, u k < 2 ^ 13) :
    val u = (u 0 + 2 ^ 13 * u 1 + 2 ^ 26 * (u 2 % 2 ^ 6)) +
      2 ^ 32 * (u 2 / 2 ^ 6 + 2 ^ 7 * u 3 + 2 ^ 20 * (u 4 % 2 ^ 12)) +
      2 ^ 64 * (u 4 / 2 ^ 12 + 2 * u 5 + 2 ^ 14 * u 6 + 2 ^ 27 * (u 7 % 2 ^ 5)) +
      2 ^ 96 * (u 7 / 2 ^ 5 + 2 ^ 8 * u 8 + 2 ^ 21 * (u 9 % 2 ^ 11)) + 2 ^ 128 * (u 9 / 2 ^ 11) := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
  have := h 8 (by decide)
  simp only [val]
  omega_using []

/-! ## The final reduction -/

/-- The carries of `h + 5` into register `r12`. -/
def chainT (u : Nat → Nat) : Nat → Nat
  | 0 => u 0 + 5
  | k + 1 => u (k + 1) + chainT u k / 2 ^ 13

/-- `Σ_{j < k} 2^(13 j) u j`. -/
def spre (u : Nat → Nat) (k : Nat) : Nat := rsum (fun j => 2 ^ (13 * j) * u j) k

theorem chainT_eq (u : Nat → Nat) : ∀ k, chainT u k = u k + (spre u k + 5) / 2 ^ (13 * k)
  | 0 => by simp [chainT, spre, rsum]
  | k + 1 => by
    rw [chainT, chainT_eq u k]
    congr 1
    have e : spre u (k + 1) + 5 = (spre u k + 5) + 2 ^ (13 * k) * u k := by
      simp only [spre, rsum]; omega_using []
    rw [e, show 13 * (k + 1) = 13 * k + 13 by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (u k)]

theorem chainT_top (u : Nat → Nat) : chainT u 9 / 2 ^ 13 = (val u + 5) / 2 ^ 130 := by
  rw [chainT_eq, Nat.add_comm (u 9)]
  have e : val u + 5 = (spre u 9 + 5) + 2 ^ 117 * u 9 := by
    simp only [val, spre, rsum]; omega_using []
  rw [e, show (130 : Nat) = 117 + 13 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), show 13 * 9 = 117 from rfl]

/-- Limbs below `2¹³` but the top one, which is masked. -/
theorem val_mask_top {g g' : Nat → Nat} (h : ∀ k < 9, g k < 2 ^ 13) (h' : ∀ k < 9, g' k = g k)
    (h9 : g' 9 = g 9 % 2 ^ 13) : val g' = val g % 2 ^ 130 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
  have := h 8 (by decide)
  have e : val g = val g' + 2 ^ 130 * (g 9 / 2 ^ 13) := by
    simp only [val, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide), h' 8 (by decide), h9]
    omega_using []
  have hl : val g' < 2 ^ 130 := by
    simp only [val, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide), h' 8 (by decide), h9]
    have : g 9 % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by decide)
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The final reduction: with `c = ⌊(h + 5) / 2¹³⁰⌋`, `(h + 5 c) mod 2¹³⁰` is `h mod p`,
for `h < 2 p`. -/
theorem reduce_eq {h : Nat} (hh : h < 2 ^ 131 - 10) :
    (h + 5 * ((h + 5) / 2 ^ 130)) % 2 ^ 130 = h % P := by
  rw [P_eq]
  rcases Nat.lt_or_ge (h + 5) (2 ^ 130) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt (by omega_using [hh, h1]), Nat.mod_eq_of_lt (by omega_using [hh, h1]), Nat.mul_zero,
      Nat.add_zero]
  · have e : (h + 5) / 2 ^ 130 = 1 := by omega_using [hh, h1]
    rw [e]
    omega_using [hh, h1, e]

/-! ## The whole final reduction -/

theorem chainT_le (u : Nat → Nat) (hu : ∀ j < 10, u j ≤ 2 ^ 13) : ∀ k < 10, chainT u k ≤ 2 ^ 13 + 5
  | 0, _ => by have := hu 0 (by decide); simp only [chainT]; omega_using [this]
  | k + 1, h => by
    have := chainT_le u hu k (by omega_using [h])
    have := hu (k + 1) h
    simp only [chainT]
    have : chainT u k / 2 ^ 13 ≤ 1 := by omega
    omega

/-- The limbs after `carry2`. -/
def redK (E : Nat → Nat) : Nat → Nat := carryN (fold E) 1 8
/-- `⌊(h + 5) / 2¹³⁰⌋`. -/
def redC (E : Nat → Nat) : Nat := (val (redK E) + 5) / 2 ^ 130
/-- The limbs after `addC`. -/
def redK' (E : Nat → Nat) : Nat → Nat := fun j => if j = 0 then redK E 0 + 5 * redC E else redK E j
/-- The limbs after `carry3`. -/
def redL (E : Nat → Nat) : Nat → Nat :=
  fun j => if j = 9 then carryN (redK' E) 0 9 9 % 2 ^ 13 else carryN (redK' E) 0 9 j

theorem red_facts (E : Nat → Nat) (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) :
    (∀ j < 10, fold E j < 2 ^ 32 - 2 ^ 19) ∧ (∀ j < 10, redK E j ≤ 2 ^ 13) ∧
      (∀ j < 10, redK' E j < 2 ^ 32 - 2 ^ 19) ∧ val (redL E) = val E % P ∧
      ∀ j < 10, redL E j < 2 ^ 13 := by
  obtain ⟨hv, hvl, h0, h1, hj⟩ := fold_facts E hE
  have hH : ∀ j < 10, fold E j < 2 ^ 32 - 2 ^ 19 := fun j hj' => by
    rcases Nat.lt_or_ge j 2 with h | h
    · rcases (by omega_using [hj', h] : j = 0 ∨ j = 1) with rfl | rfl <;> omega_using [h1, h0]
    · have := hj j h hj'; omega_using [this]
  have hvK : val (redK E) = val (fold E) := val_carryN _ 1 8 (by decide)
  have hK0 : redK E 0 = fold E 0 := carryN_below _ 1 8 0 (by decide)
  have hKm : ∀ j, 1 ≤ j → j < 9 → redK E j < 2 ^ 13 := fun j a b => carryN_lt _ 1 8 j a (by omega_using [b])
  have hK9 : redK E 9 ≤ 2 ^ 13 := by
    have : 2 ^ 117 * redK E 9 ≤ val (redK E) := by simp only [val]; omega_using [h0, hK0]
    omega_using [hvl, hvK, this]
  have hK : ∀ j < 10, redK E j ≤ 2 ^ 13 := fun j hj' => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rcases Nat.lt_or_ge j 1 with h' | h'
      · rw [show j = 0 by omega_using [hj', h, h'], hK0]; omega_using [h0, hK0]
      · have := hKm j h' h; omega_using [this]
    · rw [show j = 9 by omega_using [hj', h]]; exact hK9
  have hc : redC E ≤ 1 := by simp only [redC]; omega_using [hvl, hvK]
  have hK' : ∀ j < 10, redK' E j < 2 ^ 32 - 2 ^ 19 := fun j hj' => by
    have := hK j hj'
    simp only [redK']; split <;> omega_using [h0, hK0, hc, this]
  have hl : ∀ j < 9, carryN (redK' E) 0 9 j < 2 ^ 13 := fun j hj' => carryN_lt _ 0 9 j (by omega_using [hj']) (by omega_using [hj'])
  refine ⟨hH, hK, hK', ?_, fun j hj' => ?_⟩
  · have hm := val_mask_top (g := carryN (redK' E) 0 9) (g' := redL E) hl
      (fun k hk => by simp only [redL]; rw [iteF (by omega_using [hk])]) (by simp only [redL, ↓reduceIte, Nat.reducePow])
    rw [hm, val_carryN _ 0 9 (by decide)]
    have e : val (redK' E) = val (redK E) + 5 * redC E := by
      simp (config := {decide := true}) only [val, redK', iteT, ite_false]; omega_using []
    rw [e, redC, reduce_eq (by omega_using [hvl, hvK, e]), hvK, hv]
  · simp only [redL]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact hl j (by omega)

/-! ## Clamping -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp only [Nat.testBit_and]

/-- The clamped `r` of a key stored as four little-endian words. -/
theorem clamp_words {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    VG.Spec.Poly1305.clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by omega_using []
  rw [VG.Spec.Poly1305.clamp, e, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) from rfl,
    land_split32 h0 (by decide), land_split32 h1 (by decide), land_split32 h2 (by decide)]

theorem and_lt {k m : Nat} (h : m < 2 ^ 28) : (k &&& m) < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right h

theorem and_fffffffc_mod (k : Nat) : (k &&& 0x0ffffffc) % 2 = 0 := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc &&& 2 ^ 1 - 1 : Nat) = 0 by decide, Nat.and_zero]

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: common lemmas

Untrusted: everything here is checked by Lean. Facts about the registers the
code uses, which registers a piece of code may change (`Keeps`), and WP
rules for one instruction at a time that expose only what changes.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-! ## Registers -/

theorem yr_ne : ∀ k < 9, yr k ≠ .r0 ∧ yr k ≠ .r1 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide +kernel
theorem yr9 : yr 9 = .r1 := rfl
theorem yr_ne' : ∀ k < 10, yr k ≠ .r0 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide +kernel
theorem yr_inj : ∀ j < 10, ∀ k < 10, yr j = yr k → j = k := by decide +kernel
theorem xr_ne : ∀ k < 10, xr k ≠ .r0 ∧ xr k ≠ .r1 ∧ xr k ≠ .r2 := by decide +kernel
theorem xr_inj : ∀ j < 10, ∀ k < 10, xr j = xr k → j = k := by decide +kernel
theorem yr_eq_xr : ∀ k < 9, yr k = xr k := by decide +kernel
theorem xr9 : xr 9 = .r12 := rfl

/-- The registers `r1`–`r12`: every register the code changes but `r0` and `lr`. -/
def work : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem yr_work : ∀ k < 10, yr k ∈ work := by decide +kernel
theorem xr_work : ∀ k < 10, xr k ∈ work := by decide +kernel

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws` and the flags. -/
structure Keeps (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (ws : List Reg) (s : State) : Keeps ws s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps ws s₁ s₂) (h₂ : Keeps ws s₂ s₃) :
    Keeps ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.mono {ws ws' : List Reg} {s s' : State} (h : Keeps ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Keeps ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, subFlags, BitVec.ofNat_eq_ofNat, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.keeps {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Keeps ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.mem, h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  z : s'.z = s.z

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp only [Op2.eval, h, ↓reduceIte]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp only [exec, ho, Option.map_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp only [exec, ho, ↓reduceIte, State.load8, hin, Option.map_some])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp only [exec, ho, ↓reduceIte, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

/-! ## 32-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 32) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem toNat_and_mask (x : BitVec 32) : (x &&& (0x1fff#16).setWidth 32).toNat = x.toNat % 2 ^ 13 := by
  rw [BitVec.toNat_and, show ((0x1fff#16).setWidth 32).toNat = 2 ^ 13 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## Addresses -/

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k := Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

/-- Reading a word after writing one elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by decide) (by decide) h) (by decide)

theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by omega_using [h3])

theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ := Offset.disjoint p h (by omega_using [ha]) (by omega_using [hb])

theorem sub_sub (p : Addr) {a len b len' : Nat} (h1 : b ≤ a) (h2 : a + len ≤ b + len')
    (_h3 : b + len' < 2 ^ 32) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p + BitVec.ofNat 64 b, len'⟩ := Offset.sub p h1 h2

/-! ## The state -/

/-- The state's region. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 128⟩

theorem ea {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {off : Nat} (h : off < 128) :
    State.addr (st + BitVec.ofNat 32 off) = State.addr st + BitVec.ofNat 64 off :=
  addr_add (by omega_using [hfit, h])

theorem inSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, List.mem_append_right _ hw, contains_off h (by omega_using [h])⟩

theorem outSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions s.wr (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, hw, contains_off h (by omega_using [h])⟩

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Reduce`.
section

section

/-!
# Poly1305 on 32-bit ARM: adding the limbs of four words to the columns

Untrusted: everything here is checked by Lean. `addWords` adds limbs 0–8 of
the 16 bytes at `r1` to `r3`–`r11`, piece by piece (`piece_ok`), and leaves
the last word in `r2` (`addWords_ok`); as numbers, the limbs are `mlimb`.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- What piece `p` of the word `w` adds to its column. -/
def pieceBV (w : BitVec 32) : Nat × Nat × Nat → BitVec 32
  | (_, 0, b) => w >>> b
  | (_, a, b) => (w <<< a) >>> b

/-- What the pieces `l` of the word `w` add to column `k`. -/
def contrib : List (Nat × Nat × Nat) → Nat → BitVec 32 → BitVec 32
  | [], _, _ => 0
  | p :: ps, k, w => (if p.1 = k then pieceBV w p else 0) + contrib ps k w

/-- The columns' registers. -/
def yregs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem yr_yregs : ∀ k < 9, yr k ∈ yregs := by decide +kernel

theorem zadd (x : BitVec 32) : 0 + x = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add]
theorem addz (x : BitVec 32) : x + 0 = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]

theorem piece_ok (p : Nat × Nat × Nat) (hk : p.1 < 9) (ha : p.2.1 ≤ 31) (hb : 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr (yr p.1) = s.gpr (yr p.1) + pieceBV (s.gpr .r2) p →
      Keeps [yr p.1, .r12] s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (piece p ++ rest)) s Q := by
  obtain ⟨c, a, b⟩ := p
  simp only at hk ha hb k
  have hne := yr_ne c hk
  cases a with
  | zero =>
    simp only [piece, List.cons_append, List.nil_append]
    exact wp_add (op2_lsr hb) fun s1 u1 => k s1 u1.gpr (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))
  | succ a =>
    simp only [piece, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsl ⟨by omega_using [ha], ha⟩) fun s1 u1 => wp_add (op2_lsr hb) fun s2 u2 => ?_
    refine k s2 ?_ ((u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])))
    rw [u2.gpr, u1.gpr, u1.other _ hne.2.2.2]
    rfl

theorem pieces_ok (l : List (Nat × Nat × Nat))
    (hl : ∀ p ∈ l, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ j < 9, s'.gpr (yr j) = s.gpr (yr j) + contrib l j (s.gpr .r2)) →
      Keeps (.r12 :: yregs) s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l.flatMap piece ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s (fun j _ => by simp only [contrib, BitVec.ofNat_eq_ofNat, BitVec.add_zero]) (Keeps.refl _ _)
  | cons p ps ih =>
    have hp := hl p List.mem_cons_self
    rw [List.flatMap_cons, List.append_assoc]
    refine piece_ok p hp.1 hp.2.1 hp.2.2 fun s1 h1 k1 => ?_
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) fun s2 h2 k2 => k s2 (fun j hj => ?_) ?_
    · have e2 : s1.gpr .r2 = s.gpr .r2 := k1.gpr _ (by have := yr_ne p.1 hp.1; simp only [List.mem_cons, this.2.2.1.symm, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true])
      rw [h2 j hj, e2, contrib]
      by_cases e : p.1 = j
      · subst e; rw [h1]; simp only [ite_true, BitVec.add_assoc]
      · have e1 : s1.gpr (yr j) = s.gpr (yr j) := k1.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => e (yr_inj _ (by omega_using [hj]) _ (by omega_using [hp]) h).symm, (yr_ne j hj).2.2.2⟩)
        rw [e1]; simp only [e, ite_false, zadd]
    · exact (k1.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_cons_of_mem _ (yr_yregs _ hp.1)
        · exact List.mem_cons_self).trans k2

theorem pieces_valid : ∀ i < 4, ∀ p ∈ pieces i, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31 := by
  decide

/-- The words at `r1`. -/
def word (s : State) (i : Nat) : BitVec 32 :=
  s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 32

/-- What words `0, …, i - 1` add to column `k`. -/
def wsum (w : Nat → BitVec 32) : Nat → Nat → BitVec 32
  | 0, _ => 0
  | i + 1, k => wsum w i k + contrib (pieces i) k (w i)

/-- After words `< i` (the registers relative to `s₀`). -/
structure WI (s₀ : State) (i : Nat) (s : State) : Prop where
  cols : ∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + wsum (word s₀) i j
  r2 : 0 < i → s.gpr .r2 = word s₀ (i - 1)
  keeps : Keeps (.r2 :: .r12 :: yregs) s₀ s

theorem addWord_step {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4)
    (i : Nat) (s : State) (hi : i < 4) (h : WI s₀ i s) : WP isa (.block (addWord i)) s (WI s₀ (i + 1)) := by
  have e1 : s.gpr .r1 = s₀.gpr .r1 := h.keeps.gpr _ (by decide)
  rw [addWord, ← List.append_nil ((pieces i).flatMap piece)]
  refine wp_ldr (by omega_using [hi]) rfl (by rw [e1, h.keeps.rd, h.keeps.wr]; exact hin i hi) fun s1 u1 => ?_
  have hw : s1.gpr .r2 = word s₀ i := by rw [u1.gpr, e1, h.keeps.mem]; rfl
  refine pieces_ok _ (pieces_valid i hi) fun s2 h2 k2 => WP.block_nil ⟨fun j hj => ?_, fun _ => ?_, ?_⟩
  · rw [h2 j hj, hw, u1.other _ (yr_ne j hj).2.2.1, h.cols j hj, wsum, BitVec.add_assoc]
  · rw [k2.gpr _ (by decide), hw]; rfl
  · exact h.keeps.trans ((u1.keeps (by simp only [List.mem_cons, reduceCtorEq, false_or, true_or])).trans (k2.mono fun r hr => List.mem_cons_of_mem _ hr))

theorem addWords_ok {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block addWords) s₀ fun s =>
      (∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + wsum (word s₀) 4 j) ∧ s.gpr .r2 = word s₀ 3 ∧
      Keeps (.r2 :: .r12 :: yregs) s₀ s := by
  refine WP.mono (wp_range_flatMap (M := isa) (WI s₀) (addWord_step hin) 4 (Nat.le_refl _) s₀
    ⟨fun j _ => by simp only [wsum, BitVec.ofNat_eq_ofNat, BitVec.add_zero], fun h => absurd h (by decide), Keeps.refl _ _⟩)
    fun s h => ⟨h.cols, h.r2 (by decide), h.keeps⟩

/-! ## The limbs as numbers -/

/-- The limbs `addWords` adds, as numbers. -/
theorem shl_mod (Y a : Nat) (ha : a ≤ 32) : Y * 2 ^ a % 2 ^ 32 = 2 ^ a * (Y % 2 ^ (32 - a)) := by
  rw [show (2 : Nat) ^ 32 = 2 ^ (32 - a) * 2 ^ a by rw [← Nat.pow_add, Nat.sub_add_cancel ha],
    Nat.mul_mod_mul_right, Nat.mul_comm]

/-- `X + 2ᵃ Y` fits `n` bits. -/
theorem fits {X Y a c n : Nat} (hx : X < 2 ^ a) (hy : Y < 2 ^ c) (h : a + c ≤ n) :
    X + 2 ^ a * Y < 2 ^ n := by
  have h1 : 2 ^ a * Y + 2 ^ a ≤ 2 ^ a * 2 ^ c := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  have h2 : 2 ^ a * 2 ^ c ≤ 2 ^ n := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) h
  omega_using [hx, h1, h2]

theorem modlt {Y c k : Nat} (hy : Y < 2 ^ c) : Y % 2 ^ k < 2 ^ c :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) hy

theorem modw {Y c k : Nat} (hy : Y < 2 ^ c) (h : 2 ^ c ≤ 2 ^ k) : Y % 2 ^ k = Y :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy h)

theorem shl_shr_le (x : BitVec 32) {a b : Nat} (h : a ≤ b) (ha : a ≤ 32) :
    ((x <<< a) >>> b).toNat = x.toNat % 2 ^ (32 - a) / 2 ^ (b - a) := by
  rw [toNat_shr, toNat_shl, shl_mod _ _ ha,
    show (2 : Nat) ^ b = 2 ^ a * 2 ^ (b - a) by rw [← Nat.pow_add, Nat.add_sub_cancel' h],
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]

theorem shl_shr_ge (x : BitVec 32) {a b : Nat} (h : b ≤ a) (ha : a ≤ 32) :
    ((x <<< a) >>> b).toNat = x.toNat % 2 ^ (32 - a) * 2 ^ (a - b) := by
  rw [toNat_shr, toNat_shl, shl_mod _ _ ha,
    show (2 : Nat) ^ a = 2 ^ b * 2 ^ (a - b) by rw [← Nat.pow_add, Nat.add_sub_cancel' h],
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_comm]

theorem add_piece (x y : BitVec 32) {a b c : Nat} (hba : b ≤ a) (ha : a ≤ 32) (hc : 32 - c = a - b)
    (hc' : c ≤ 32) :
    (x >>> c + (y <<< a) >>> b).toNat = x.toNat / 2 ^ c + y.toNat % 2 ^ (32 - a) * 2 ^ (a - b) := by
  rw [BitVec.toNat_add, toNat_shr, shl_shr_ge _ hba ha]
  apply Nat.mod_eq_of_lt
  have h1 : x.toNat / 2 ^ c < 2 ^ (a - b) := by
    rw [← hc]; apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_sub_cancel' hc']; exact x.isLt
  have := fits h1 (Nat.mod_lt y.toNat (Nat.two_pow_pos (32 - a))) (show a - b + (32 - a) ≤ 32 by omega_using [hba, ha])
  rwa [Nat.mul_comm] at this

set_option linter.unusedSimpArgs false in
theorem wsum_toNat (w : Nat → BitVec 32) {k : Nat} (hk : k < 9) :
    (wsum w 4 k).toNat = mlimb (w 0).toNat (w 1).toNat (w 2).toNat (w 3).toNat k := by
  simp only [wsum, contrib, pieces, pieceBV, zadd, addz]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp only [mlimb, Nat.reduceEqDiff, ite_true, ite_false, zadd, addz, toNat_shr,
    shl_shr_le _ (show 19 ≤ 19 by decide) (by decide), shl_shr_le _ (show 6 ≤ 19 by decide) (by decide),
    shl_shr_le _ (show 12 ≤ 19 by decide) (by decide), shl_shr_le _ (show 18 ≤ 19 by decide) (by decide),
    shl_shr_le _ (show 5 ≤ 19 by decide) (by decide), shl_shr_le _ (show 11 ≤ 19 by decide) (by decide),
    shl_shr_ge _ (show 19 ≤ 25 by decide) (by decide), shl_shr_ge _ (show 19 ≤ 31 by decide) (by decide),
    shl_shr_ge _ (show 19 ≤ 24 by decide) (by decide), Nat.reduceSub]
  all_goals first
    | exact Nat.div_one _
    | exact (add_piece _ _ (by decide) (by decide) (by decide) (by decide)).trans rfl

end VG.Proof.Poly1305.Arm

end

section

/-!
# Poly1305 on 32-bit ARM: carrying and the final reduction

Untrusted: everything here is checked by Lean. The columns (or limbs) are in
`r3`–`r11` and `r1` (`Cols`); `carryStep` moves a column's bits from 13 up
to the next column (`carries_ok`), `carryFold` carries them all into `fold`
(`carryFold_ok`), and `reduce` reduces them fully (`reduceRegs_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The columns (or limbs) are `v`, in `r3`–`r11` and `r1`. -/
def Cols (v : Nat → Nat) (s : State) : Prop := ∀ j < 10, (s.gpr (yr j)).toNat = v j

/-- The mask `movw r2, #0x1fff` leaves in `r2`. -/
abbrev maskV : BitVec 32 := (0x1fff#16).setWidth 32

/-- The registers of the columns. -/
def cregs : List Reg := .r1 :: yregs

theorem yr_cregs : ∀ k < 10, yr k ∈ cregs := by decide +kernel

theorem cregs_r2 : Reg.r2 ∉ cregs := by decide
theorem cregs_r12 : Reg.r12 ∉ cregs := by decide
theorem cregs_r0 : Reg.r0 ∉ cregs := by decide

theorem carryStep_ok {k : Nat} (hk : k < 9) {s : State} (hm : s.gpr .r2 = maskV)
    (hb : (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 < 2 ^ 32) :
    WP isa (.block (carryStep k)) s fun s' =>
      (s'.gpr (yr (k + 1))).toNat = (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 ∧
      (s'.gpr (yr k)).toNat = (s.gpr (yr k)).toNat % 2 ^ 13 ∧ Keeps [yr k, yr (k + 1)] s s' := by
  have hne : yr k ≠ yr (k + 1) := fun h => absurd (yr_inj _ (by omega_using [hk]) _ (by omega_using [hk]) h) (by omega_using [])
  have h2 : yr k ≠ .r2 := (yr_ne k hk).2.2.1
  refine wp_add (op2_lsr (by decide)) fun s1 u1 => wp_and (op2_reg _ _) fun s2 u2 => WP.block_nil ?_
  refine ⟨?_, ?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))⟩
  · rw [u2.other _ hne.symm, u1.gpr, toNat_add_lt (by rw [toNat_shr]; exact hb), toNat_shr]
  · rw [u2.gpr, u1.other _ hne, u1.other _ (Ne.symm (yr_ne' (k + 1) (by omega_using [hk])).2.1), hm, toNat_and_mask]

/-- After the carries from columns `a`, …, `a + k - 1`. -/
structure CI (f : Nat → Nat) (a : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  cols : Cols (carryN f a k) s
  keeps : Keeps cregs s₀ s

theorem carries_ok (a n : Nat) (hn : n + a ≤ 9) {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19)
    {s : State} (hc : Cols f s) (hm : s.gpr .r2 = maskV) :
    WP isa (.block ((List.range n).flatMap fun k => carryStep (k + a))) s fun s' =>
      Cols (carryN f a n) s' ∧ Keeps cregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (CI f a s) (fun k s' hk h => ?_) n (Nat.le_refl _) s
    ⟨hc, Keeps.refl _ _⟩) fun s' h => ⟨h.cols, h.keeps⟩
  have hm' : s'.gpr .r2 = maskV := by rw [h.keeps.gpr _ cregs_r2, hm]
  have hb := carryN_step_lt f a hf k (by omega_using [hn, hk])
  refine WP.mono (carryStep_ok (k := k + a) (by omega_using [hn, hk]) hm' (by
    rw [h.cols _ (by omega_using [hn, hk]), h.cols _ (by omega_using [hn, hk])]; exact hb)) fun s'' ⟨e1, e0, hk⟩ => ⟨?_, ?_⟩
  · intro j hj
    simp only [carryN, cstep]
    by_cases ej : j = k + a
    · subst ej; rw [iteT rfl, e0, h.cols _ hj]
    by_cases ej' : j = k + a + 1
    · subst ej'; rw [iteF ej, iteT rfl, e1, h.cols _ hj, h.cols _ (by omega_using [hj])]
    · rw [iteF ej, iteF ej', hk.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => ej (yr_inj _ hj _ (by omega) e), fun e => ej' (yr_inj _ hj _ (by omega) e)⟩),
        h.cols _ hj]
  · exact h.keeps.trans (hk.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact yr_cregs _ (by omega))

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: carrying all columns, the final reduction, and words

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

theorem Cols.keep {v : Nat → Nat} {s s' : State} (h : Cols v s) {ws : List Reg} (hk : Keeps ws s s')
    (hw : ∀ j < 10, yr j ∉ ws) : Cols v s' := fun j hj => by rw [hk.gpr _ (hw j hj)]; exact h j hj

theorem carryFold_ok {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) {s : State} (hc : Cols f s) :
    WP isa (.block carryFold) s fun s' =>
      Cols (fold f) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  rw [carryFold, List.cons_append, List.cons_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Cols f s1 := hc.keep (u1.keeps (List.mem_singleton_self _)) fun j hj => by
    simpa using (yr_ne' j hj).2.1
  rw [List.append_assoc]
  refine WP.append (carries_ok 0 9 (by decide) hf hc1 u1.gpr) fun s2 ⟨hc2, k2⟩ => ?_
  have hl := fun j (hj : j < 9) => carryN_lt f 0 9 j (by omega_using [hj]) (by omega_using [hj])
  have hF9 := hc2 9 (by decide)
  have hF0 := hc2 0 (by decide)
  have hF1 := hc2 1 (by decide)
  simp only [yr] at hF9 hF0 hF1
  have hm2 : s2.gpr .r2 = maskV := by rw [k2.gpr _ cregs_r2, u1.gpr]; rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_and (op2_reg _ _) fun s4 u4 => ?_
  refine wp_add (op2_lsl (by decide)) fun s5 u5 => wp_add (op2_reg _ _) fun s6 u6 => ?_
  -- The values of `r12`, `r1` and `r3`.
  have hc9 : (s3.gpr .r12).toNat = carryN f 0 9 9 / 2 ^ 13 := by rw [u3.gpr, toNat_shr, hF9]
  have hc9' : carryN f 0 9 9 / 2 ^ 13 < 2 ^ 19 := by have := (s2.gpr .r1).isLt; omega_using [hF9, hc9]
  have h12 : (s5.gpr .r12).toNat = 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    rw [u5.gpr, u4.other _ (by decide), toNat_add_lt (by rw [toNat_shl]; omega_using [hc9, hc9']), toNat_shl, hc9]
    omega_using [hc9, hc9']
  have h1 : (s6.gpr .r1).toNat = carryN f 0 9 9 % 2 ^ 13 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide),
      u3.other _ (by decide), hm2, toNat_and_mask, hF9]
  have h3 : (s6.gpr .r3).toNat = carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    have := hl 0 (by decide)
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      toNat_add_lt (by rw [h12, hF0]; omega_using [hF0, hc9, hc9', this]), h12, hF0]
  have h4 : (s6.gpr .r4).toNat = carryN f 0 9 1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hF1]
  have hm6 : s6.gpr .r2 = maskV := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hm2]
  have hk6 : Keeps (.r2 :: .r12 :: cregs) s s6 :=
    (u1.keeps (by simp only [List.mem_cons, reduceCtorEq, false_or, true_or])).trans ((k2.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans ((u3.keeps (by simp only [List.mem_cons, reduceCtorEq, true_or, or_true])).trans
      ((u4.keeps (by simp only [cregs, List.mem_cons, reduceCtorEq, true_or, or_true])).trans ((u5.keeps (by simp only [List.mem_cons, reduceCtorEq, true_or, or_true])).trans (u6.keeps (by simp only [cregs, yregs, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]))))))
  refine WP.mono (carryStep_ok (k := 0) (by decide) hm6 (by
    simp only [yr, Nat.zero_add]; rw [h3, h4]; have := hl 1 (by decide); omega_using [hF1, h3, h4, this]))
    fun s7 ⟨e1, e0, k7⟩ => ⟨fun j hj => ?_, ?_, hk6.trans (k7.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [yr, cregs, yregs])⟩
  · simp only [Nat.zero_add] at e1 e0
    rcases Nat.lt_or_ge j 2 with h | h
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega_using [hj, h]
      · rw [e0, fold_0]; simp only [yr] at h3 ⊢; rw [h3]
      · rw [e1, fold_1]; simp only [yr] at h3 h4 ⊢; rw [h3, h4]
    have k26 : Keeps [.r12, .r1, .r3] s2 s6 :=
      (u3.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans ((u4.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true])).trans ((u5.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans
        (u6.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]))))
    rcases Nat.lt_or_ge j 9 with h' | h'
    · have hn : ∀ j < 9, 2 ≤ j → yr j ∉ [Reg.r12, .r1, .r3] ∧ yr j ∉ [yr 0, yr (0 + 1)] := by decide +kernel
      rw [k7.gpr _ (hn j h' h).2, k26.gpr _ (hn j h' h).1, fold_mid f h h']
      exact hc2 j hj
    · rw [show j = 9 by omega_using [hj, h, h'], k7.gpr _ (by decide), fold_9]; exact h1
  · rw [k7.gpr _ (by simp only [yr, Nat.zero_add, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]), hm6]

theorem plus5_ok {K : Nat → Nat} (hK : ∀ j < 10, K j ≤ 2 ^ 13) {s : State} (hc : Cols K s) :
    WP isa (.block plus5) s fun s' => (s'.gpr .r12).toNat = chainT K 9 ∧ Keeps [.r12] s s' := by
  rw [plus5]
  refine wp_add (op2_imm (by decide)) fun s1 u1 => ?_
  have h0 := hc 0 (by decide)
  have hK0 := hK 0 (by decide)
  simp only [yr] at h0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => (s'.gpr .r12).toNat = chainT K k ∧ Keeps [.r12] s1 s')
    (fun k s' hk ⟨h12, hk'⟩ => ?_) 9 (Nat.le_refl _) s1
    ⟨by rw [u1.gpr, toNat_add_lt (by rw [h0]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega_using [hK0, h0]), h0]; rfl, Keeps.refl _ _⟩)
    fun s' ⟨h, k⟩ => ⟨h, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans k⟩
  have hy : (s'.gpr (yr (k + 1))).toNat = K (k + 1) := by
    rw [hk'.gpr _ (by have := (yr_ne' (k + 1) (by omega_using [hk])).2.2; simpa using this),
      u1.other _ (yr_ne' (k + 1) (by omega_using [hk])).2.2]
    exact hc (k + 1) (by omega_using [hk])
  have hle := chainT_le K hK k (by omega_using [hk])
  have hle' := hK (k + 1) (by omega_using [hk])
  refine wp_add (op2_lsr (by decide)) fun s2 u2 => WP.block_nil ⟨?_, hk'.trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))⟩
  rw [u2.gpr, toNat_add_lt (by rw [toNat_shr, hy, h12]; omega_using [hy, hle, hle']), toNat_shr, hy, h12]
  rfl

theorem addC_ok {s : State} {t k0 : Nat} (ht : (s.gpr .r12).toNat = t) (ht' : t < 2 ^ 20)
    (h3 : (s.gpr .r3).toNat = k0) (hk0 : k0 < 2 ^ 20) :
    WP isa (.block addC) s fun s' => (s'.gpr .r3).toNat = k0 + 5 * (t / 2 ^ 13) ∧
      Keeps [.r12, .r3] s s' := by
  rw [addC]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => wp_add (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_add (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans
    ((u2.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans (u3.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])))⟩
  have e1 : (s1.gpr .r12).toNat = t / 2 ^ 13 := by rw [u1.gpr, toNat_shr, ht]
  have e2 : (s2.gpr .r12).toNat = 5 * (t / 2 ^ 13) := by
    rw [u2.gpr, toNat_add_lt (by rw [toNat_shl, e1]; omega_using [ht, ht']), toNat_shl, e1]; omega_using [ht, ht']
  rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide),
    toNat_add_lt (by rw [h3, e2]; omega_using [ht, ht', h3, hk0, e1]), h3, e2]

theorem reduceRegs_ok {E : Nat → Nat} (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) {s : State}
    (hc : Cols E s) :
    WP isa (.block reduceRegs) s fun s' =>
      Cols (redL E) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  obtain ⟨hH, hK, hK', -, -⟩ := red_facts E hE
  rw [reduceRegs]
  simp only [List.append_assoc]
  refine WP.append (carryFold_ok hE hc) fun s1 ⟨hc1, hm1, k1⟩ => ?_
  refine WP.append (carries_ok 1 8 (by decide) hH hc1 hm1) fun s2 ⟨hc2, k2⟩ => ?_
  refine WP.append (plus5_ok hK hc2) fun s3 ⟨h12, k3⟩ => ?_
  have hc3 : Cols (redK E) s3 := hc2.keep k3 fun j hj => by simpa using (yr_ne' j hj).2.2
  have ht : chainT (redK E) 9 < 2 ^ 20 := by have := chainT_le _ hK 9 (by decide); omega_using [this]
  have h30 : (s3.gpr .r3).toNat = redK E 0 := hc3 0 (by decide)
  have hk0 := hK 0 (by decide)
  refine WP.append (addC_ok h12 ht h30 (by omega_using [h30, hk0])) fun s4 ⟨h4, k4⟩ => ?_
  have hc4 : Cols (redK' E) s4 := fun j hj => by
    simp only [redK']
    split
    · rename_i e; subst e; show (s4.gpr .r3).toNat = _; rw [h4, chainT_top]; rfl
    · rw [k4.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(yr_ne' j hj).2.2, fun e => by have := yr_inj _ hj 0 (by decide) e; omega⟩)]
      exact hc3 j hj
  have hm4 : s4.gpr .r2 = maskV := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ cregs_r2, hm1]
  rw [carry3]
  refine WP.append (carries_ok 0 9 (by decide) hK' hc4 hm4) fun s5 ⟨hc5, k5⟩ => ?_
  have hm5 : s5.gpr .r2 = maskV := by rw [k5.gpr _ cregs_r2, hm4]
  refine wp_and (op2_reg _ _) fun s6 u6 => WP.block_nil ⟨fun j hj => ?_, ?_, ?_⟩
  · simp only [redL]
    split
    · rename_i e; subst e
      have := hc5 9 (by decide)
      simp only [yr] at this ⊢
      rw [u6.gpr, hm5, toNat_and_mask, this]
    · rw [u6.other _ (fun e => by have := yr_inj _ hj 9 (by decide) e; omega)]
      exact hc5 j hj
  · rw [u6.other _ (by decide), hm5]
  · refine k1.trans ((k2.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans ((k3.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, reduceCtorEq, true_or, or_true])).trans
      ((k4.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, cregs, yregs, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self])).trans ((k5.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans
        (u6.keeps (by simp only [cregs, List.mem_cons, reduceCtorEq, true_or, or_true]))))))

/-- The words of the limbs `L` (see `val_toWords`). -/
def tw0 (L : Nat → Nat) : Nat := L 0 + 2 ^ 13 * L 1 + 2 ^ 26 * (L 2 % 2 ^ 6)
def tw1 (L : Nat → Nat) : Nat := L 2 / 2 ^ 6 + 2 ^ 7 * L 3 + 2 ^ 20 * (L 4 % 2 ^ 12)
def tw2 (L : Nat → Nat) : Nat := L 4 / 2 ^ 12 + 2 * L 5 + 2 ^ 14 * L 6 + 2 ^ 27 * (L 7 % 2 ^ 5)
def tw3 (L : Nat → Nat) : Nat := L 7 / 2 ^ 5 + 2 ^ 8 * L 8 + 2 ^ 21 * (L 9 % 2 ^ 11)

theorem add_shl {x y : BitVec 32} {a : Nat} (h : x.toNat + y.toNat * 2 ^ a % 2 ^ 32 < 2 ^ 32) :
    (x + y <<< a).toNat = x.toNat + y.toNat * 2 ^ a % 2 ^ 32 := by
  rw [toNat_add_lt (by rw [toNat_shl]; exact h), toNat_shl]

theorem shr' {x : BitVec 32} {n X : Nat} (hx : x.toNat = X) : (x >>> n).toNat = X / 2 ^ n := by
  rw [toNat_shr, hx]

/-- `x + (y << a)`, where `x` has `a` bits: the bits of `y` that fit above them. -/
theorem add_shl2 {x y : BitVec 32} {a X Y : Nat} (hx : x.toNat = X) (hy : y.toNat = Y)
    (ha : a ≤ 32) (hX : X < 2 ^ a) : (x + y <<< a).toNat = X + 2 ^ a * (Y % 2 ^ (32 - a)) := by
  rw [BitVec.toNat_add, toNat_shl, hx, hy, shl_mod _ _ ha]
  exact Nat.mod_eq_of_lt (fits hX (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega_using [ha]))

theorem toWords_ok {L : Nat → Nat} {s : State} (hc : Cols L s) (hL : ∀ j < 9, L j < 2 ^ 13) :
    WP isa (.block toWords) s fun s' =>
      (s'.gpr .r3).toNat = tw0 L ∧ (s'.gpr .r5).toNat = tw1 L ∧ (s'.gpr .r7).toNat = tw2 L ∧
      (s'.gpr .r10).toNat = tw3 L ∧ (s'.gpr .r1).toNat = L 9 / 2 ^ 11 ∧
      Keeps [.r1, .r3, .r5, .r7, .r10] s s' := by
  have c0 := hc 0 (by decide); have c1 := hc 1 (by decide); have c2 := hc 2 (by decide)
  have c3 := hc 3 (by decide); have c4 := hc 4 (by decide); have c5 := hc 5 (by decide)
  have c6 := hc 6 (by decide); have c7 := hc 7 (by decide); have c8 := hc 8 (by decide)
  have c9 := hc 9 (by decide)
  simp only [yr] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have l0 := hL 0 (by decide); have l1 := hL 1 (by decide); have l2 := hL 2 (by decide)
  have l3 := hL 3 (by decide); have l4 := hL 4 (by decide); have l5 := hL 5 (by decide)
  have l6 := hL 6 (by decide); have l7 := hL 7 (by decide); have l8 := hL 8 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [toWords, runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [add_shl2 (add_shl2 c0 c1 (by decide) l0) c2 (by decide) (fits l0 (modlt l1) (by decide)),
      modw l1 (by decide)]
    rfl
  · have x0 : L 2 / 2 ^ 6 < 2 ^ 7 := Nat.div_lt_of_lt_mul l2
    rw [add_shl2 (add_shl2 (shr' c2) c3 (by decide) x0) c4 (by decide)
      (fits x0 (modlt l3) (by decide)), modw l3 (by decide)]
    rfl
  · have x0 : L 4 / 2 ^ 12 < 2 ^ 1 := Nat.div_lt_of_lt_mul l4
    have x1 := fits x0 (modlt (k := 32 - 1) l5) (show 1 + 13 ≤ 14 by decide)
    rw [add_shl2 (add_shl2 (add_shl2 (shr' c4) c5 (by decide) x0) c6 (by decide) x1) c7 (by decide)
      (fits x1 (modlt l6) (by decide)), modw l5 (by decide), modw l6 (by decide)]
    rfl
  · have x0 : L 7 / 2 ^ 5 < 2 ^ 8 := Nat.div_lt_of_lt_mul l7
    rw [add_shl2 (add_shl2 (shr' c7) c8 (by decide) x0) c9 (by decide)
      (fits x0 (modlt l8) (by decide)), modw l8 (by decide)]
    rfl
  · rw [toNat_shr, c9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h3, h5, h7, h10⟩ := hr
    simp only [h1, ↓reduceIte, h10, h7, h5, h3]

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Absorb`.
section

section

/-!
# Poly1305 on 32-bit ARM: the columns of `h r`

Untrusted: everything here is checked by Lean. `multiply` computes the
columns `col h r` (above) into `r3`–`r12`, row by row: row `j` loads
`h j` (two limbs are packed in each word at `[0, 20)`) and adds its products
with the limbs of `r` (at `rOff i`) to the columns (`mac_step`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- Limb `i` of `r` as `loadR i` loads it from the memory `m` of the state at `B`. -/
def rval (m : Mem) (B : Addr) (i : Nat) : Nat :=
  if i = 4 ∨ i = 9 then (m (B + BitVec.ofNat 64 (rOff i))).toNat
  else (m.readW (B + BitVec.ofNat 64 (rOff i)) 32).toNat

theorem rOff_lt : ∀ i < 10, rOff i + 4 ≤ 128 := by decide +kernel

/-- The bound on the limbs of `h` that are multiplied. -/
abbrev Hb : Nat := 2 ^ 13 + 2 ^ 9

theorem col_lt {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {k : Nat}
    (hk : k < 10) : col h r k ≤ 3564723200 := by
  have := col_le (h := h) (r := r) (R := 2 ^ 13 - 1) hh (fun i hi => by have := hr i hi; omega_using [this]) hk
  simp only [Hb] at this
  omega_using [this]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem macCore_ok {i : Nat} (hi : i < 10) {X : Reg} (hX2 : X ≠ .r2)
    {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hb : (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i < 2 ^ 32) :
    WP isa (.block [loadR i, .mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s fun s' =>
      (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i ∧
        Keeps [.r2, X] s s' := by
  have hro := rOff_lt i hi
  have hA : State.addr (s.gpr .r0 + BitVec.ofNat 32 (rOff i)) = State.addr st + BitVec.ofNat 64 (rOff i) := by
    rw [h0]; exact ea hfit (by omega_using [hro])
  have finish : ∀ s1 : State, ∀ v : BitVec 32, Upd s s1 .r2 v → v.toNat = rval s.mem (State.addr st) i →
      WP isa (.block [.mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s1 fun s' =>
        (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i ∧
          Keeps [.r2, X] s s' := fun s1 v u1 hv =>
    wp_mul fun s2 u2 => wp_add (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨by
      have e1 : s1.gpr .r1 = s.gpr .r1 := u1.other _ (by decide)
      have eX : s1.gpr X = s.gpr X := u1.other _ hX2
      have hp : (s2.gpr .r2).toNat = (s.gpr .r1).toNat * rval s.mem (State.addr st) i := by
        rw [u2.gpr, u1.gpr, e1, toNat_mul_lt (by rw [hv]; omega_using [hb]), hv]
      rw [u3.gpr, u2.other _ hX2, eX, toNat_add_lt (by rw [hp]; exact hb), hp],
      (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])).trans ((u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])))⟩
  by_cases h49 : i = 4 ∨ i = 9
  · simp only [loadR, h49, ite_true]
    refine wp_ldrb (by omega_using [hro]) hA (inSt hw (by omega_using [hro])) fun s1 u1 => finish s1 _ u1 ?_
    simp only [rval, h49, ite_true]
    rfl
  · simp only [loadR, h49, ite_false]
    refine wp_ldr (by omega_using [hro]) hA (inSt hw (by omega_using [hro])) fun s1 u1 => finish s1 _ u1 ?_
    simp only [rval, h49, ite_false]

/-- In row `j`, after the products of `r i` for `i < n`, relative to the state
`s₀` in which the multiplication starts. -/
structure MI (h r : Nat → Nat) (s₀ : State) (j n : Nat) (s : State) : Prop where
  cols : ∀ k < 10, (s.gpr (xr k)).toNat = psum h r j n k
  a : (s.gpr .r1).toNat = if 0 < j ∧ 10 - j < n then 5 * h j else h j
  keeps : Keeps work s₀ s

theorem mac_step {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    {j : Nat} (hj : j < 10) (n : Nat) (s : State) (hn : n < 10) (hs : MI h r s₀ j n s) :
    WP isa (.block (mac j n)) s (MI h r s₀ j (n + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hRs : rval s.mem (State.addr st) n = r n := by rw [hs.keeps.mem]; exact hR n hn
  set k₀ := (n + j) % 10 with hk₀
  have hk₀10 : k₀ < 10 := Nat.mod_lt _ (by decide)
  have hX := xr_ne k₀ hk₀10
  -- The core, from a state with `r1 = a` and the columns and memory of `s`.
  have core : ∀ s1 : State, Keeps [.r1] s s1 →
      (s1.gpr .r1).toNat = (if n + j < 10 then h j else 5 * h j) →
      (s1.gpr .r1).toNat = (if 0 < j ∧ 10 - j < n + 1 then 5 * h j else h j) →
      WP isa (.block [loadR n, .mul .r2 .r1 .r2, .dp .add (xr k₀) (xr k₀) (.reg .r2)]) s1
        (MI h r s₀ j (n + 1)) := by
    intro s1 k1 ha ha'
    have hc1 : ∀ k < 10, (s1.gpr (xr k)).toNat = psum h r j n k := fun k hk => by
      rw [k1.gpr _ (by simpa using (xr_ne k hk).2.1)]; exact hs.cols k hk
    have e := psum_step h r hj hn hk₀10
    rw [iteT hk₀] at e
    have hle := psum_le_col h r (j := j) (n := n + 1) (k := k₀) hj
    have hcol := col_lt hh hr hk₀10
    refine WP.mono (macCore_ok hfit hn hX.2.2 (by rw [k1.gpr _ (by decide), hs0])
      (by rw [k1.wr]; exact hsw) ?_) fun s2 ⟨e2, k2⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
    · rw [k1.mem, hRs, hc1 _ hk₀10, ha, ← e]; omega_using [e, hle, hcol]
    · by_cases ek : k = k₀
      · subst ek; rw [e2, k1.mem, hRs, hc1 _ hk₀10, ha, e]
      · rw [k2.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨(xr_ne k hk).2.2, fun h' => ek (xr_inj _ hk _ hk₀10 h')⟩), hc1 k hk]
        have e' := psum_step h r hj hn hk (k := k)
        rw [iteF (by rw [← hk₀]; exact ek)] at e'
        exact e'.symm
    · rw [k2.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, hX.2.1.symm⟩)]; exact ha'
    · exact hs.keeps.trans ((k1.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, work, forall_eq, reduceCtorEq, or_self])).trans (k2.mono fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · decide
        · exact xr_work _ hk₀10))
  have hj' : h j ≤ 2 ^ 13 + 2 ^ 9 := hh j hj
  by_cases h5 : 0 < j ∧ n + j = 10
  · simp only [mac]
    rw [iteT h5, List.cons_append, List.nil_append]
    refine wp_add (op2_lsl (by decide)) fun s1 u1 => core s1 (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])) ?_ ?_
    · have ha := hs.a
      rw [iteF (by omega_using [hj, h5])] at ha
      rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, ha]; omega_using [hj', ha]), toNat_shl, ha, iteF (by omega_using [h5])]
      omega_using [hj', ha]
    · have ha := hs.a
      rw [iteF (by omega_using [hj, h5])] at ha
      rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, ha]; omega_using [hj', ha]), toNat_shl, ha, iteT (by omega_using [hj, h5])]
      omega_using [hj', ha]
  · simp only [mac, h5, ite_false, List.nil_append]
    refine core s (Keeps.refl _ _) ?_ ?_
    · rw [hs.a]; split <;> split <;> omega
    · rw [hs.a]; split <;> split <;> omega

/-- `h`, two limbs per word, at `[0, 20)` of the state at `B`. -/
def HMem (h : Nat → Nat) (m : Mem) (B : Addr) : Prop :=
  ∀ i < 5, (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat = h (2 * i) + 2 ^ 16 * h (2 * i + 1)

theorem loadH_ok {h : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) {j : Nat} (hj : j < 10) {s : State}
    (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) (hH : HMem h s.mem (State.addr st)) :
    WP isa (.block (loadH j)) s fun s' => (s'.gpr .r1).toNat = h j ∧ Keeps [.r1] s s' := by
  have hb : ∀ j < 10, h j < 2 ^ 16 := fun j hj => by have := hh j hj; simp only [Hb] at this; omega_using [this]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega_using []⟩
  · have hw' := hH i (by omega_using [hj])
    simp only [loadH, show 2 * i % 2 = 0 by omega_using [], ite_true]
    refine wp_ldr (by omega_using [hj]) (by rw [h0, show 2 * (2 * i) = 4 * i by omega_using []]; exact ea hfit (by omega_using [hj]))
      (inSt hw (by omega_using [hj])) fun s1 u1 => wp_mov (op2_lsl (by decide)) fun s2 u2 =>
        wp_mov (op2_lsr (by decide)) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans
          ((u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])))⟩
    rw [u3.gpr, u2.gpr, u1.gpr, toNat_shr, toNat_shl, hw']
    have := hb (2 * i) (by omega_using [hj]); have := hb (2 * i + 1) (by omega_using [hj])
    omega
  · have hw' := hH i (by omega_using [hj])
    simp only [loadH, show (2 * i + 1) % 2 = 1 by omega_using [], show 1 ≠ 0 by decide, ite_false,
      show 2 * i + 1 - 1 = 2 * i by omega_using [hj]]
    refine wp_ldr (by omega_using [hj]) (by rw [h0, show 2 * (2 * i) = 4 * i by omega_using []]; exact ea hfit (by omega_using [hj]))
      (inSt hw (by omega_using [hj])) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 =>
        WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))⟩
    rw [u2.gpr, u1.gpr, toNat_shr, hw']
    have := hb (2 * i) (by omega_using [hj])
    omega_using [this]

theorem row_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    (hH : HMem h s₀.mem (State.addr st)) (j : Nat) (s : State) (hj : j < 10)
    (hs : (∀ k < 10, (s.gpr (xr k)).toNat = psum h r j 0 k) ∧ Keeps work s₀ s) :
    WP isa (.block (row j)) s fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = psum h r (j + 1) 0 k) ∧ Keeps work s₀ s' := by
  obtain ⟨hc, hk⟩ := hs
  rw [row]
  refine WP.append (loadH_ok hfit hh hj (by rw [hk.gpr _ (by decide), h0]) (by rw [hk.wr]; exact hw)
    (by rw [hk.mem]; exact hH)) fun s1 ⟨ha, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (MI h r s₀ j) (fun n s' hn hs' =>
    mac_step hfit hh hr h0 hw hR hj n s' hn hs') 10 (Nat.le_refl _) s1 ⟨fun k hk' => ?_, ?_, ?_⟩)
    fun s' hs' => ⟨fun k hk' => by rw [hs'.cols k hk', psum_row], hs'.keeps⟩
  · rw [k1.gpr _ (by simpa using (xr_ne k hk').2.1)]; exact hc k hk'
  · rw [ha, iteF (by omega_using [])]
  · exact hk.trans (k1.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, work, forall_eq, reduceCtorEq, or_self]))

omit hfit in
theorem zeroX_ok {s : State} :
    WP isa (.block zeroX) s fun s' => (∀ k < 10, (s'.gpr (xr k)).toNat = 0) ∧ Keeps work s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, (s'.gpr (xr k)).toNat = 0) ∧ Keeps work s s')
    (fun n s' hn ⟨hz, hk⟩ => wp_mov (op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (xr_work n hn))⟩) 10 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (xr_inj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hz k h'
  · rw [u1.gpr]; rfl

theorem multiply_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    (hH : HMem h s₀.mem (State.addr st)) :
    WP isa (.block multiply) s₀ fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = col h r k) ∧ Keeps work s₀ s' := by
  rw [multiply]
  refine WP.append zeroX_ok fun s1 ⟨hz, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun j s => (∀ k < 10, (s.gpr (xr k)).toNat = psum h r j 0 k) ∧ Keeps work s₀ s)
    (fun j s hj hs => row_ok hfit hh hr h0 hw hR hH j s hj hs) 10 (Nat.le_refl _) s1
    ⟨fun k hk => by rw [hz k hk, psum_zero], k1⟩)
    fun s' ⟨hc, hk⟩ => ⟨fun k hk' => by rw [hc k hk', psum_ten], hk⟩

end

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: absorbing a block

Untrusted: everything here is checked by Lean. `absorb pad` adds the 16
bytes at `r1` (and `2¹²⁸` if `pad`) to the columns `D` (`D 0`–`D 8` in
`r3`–`r11`, `D 9` at `[16, 20)` of the state: `ColsD`), carries them into
`h`, packs `h` into `[0, 20)` and multiplies it by `r` (`absorb_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-- The columns `D`: `D 0`–`D 8` in `r3`–`r11`, `D 9` at `[16, 20)` of the state at `B`. -/
def ColsD (D : Nat → Nat) (B : Addr) (s : State) : Prop :=
  (∀ k < 9, (s.gpr (yr k)).toNat = D k) ∧ (s.mem.readW (B + BitVec.ofNat 64 16) 32).toNat = D 9

/-- The 128-bit number at `r1`, as `addWords` reads it. -/
def msgVal (s : State) : Nat :=
  (word s 0).toNat + 2 ^ 32 * (word s 1).toNat + 2 ^ 64 * (word s 2).toNat + 2 ^ 96 * (word s 3).toNat

/-- `s'` is `s` but for the registers `ws`, the flags and the memory in `F`. -/
structure KeepsF (ws : List Reg) (F : List Region) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  frame : Frame F s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.keepsF {ws : List Reg} {s s' : State} (h : Keeps ws s s') (F : List Region) :
    KeepsF ws F s s' := ⟨h.gpr, h.mem ▸ Frame.refl _ _, h.rd, h.wr, h.sp⟩

theorem KeepsF.trans {ws : List Reg} {F : List Region} {s₁ s₂ s₃ : State} (h₁ : KeepsF ws F s₁ s₂)
    (h₂ : KeepsF ws F s₂ s₃) : KeepsF ws F s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₁.frame.trans h₂.frame, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem KeepsF.mono {ws ws' : List Reg} {F : List Region} {s s' : State} (h : KeepsF ws F s s')
    (hs : ∀ r ∈ ws, r ∈ ws') : KeepsF ws' F s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.frame, h.rd, h.wr, h.sp⟩

/-- `[0, 20)` of the state. -/
abbrev accR (B : Addr) : Region := ⟨B, 20⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- After packing `i` words of `H`. -/
structure PI (H : Nat → Nat) (st : BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  mem : ∀ i' < i, (s.mem.readW (State.addr st + BitVec.ofNat 64 (4 * i')) 32).toNat =
    H (2 * i') + 2 ^ 16 * H (2 * i' + 1)
  cols : ∀ k < 10, 2 * i ≤ k → (s.gpr (yr k)).toNat = H k
  keeps : KeepsF work [accR (State.addr st)] s₀ s

theorem pack_step {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s₀ : State} (h0 : s₀.gpr .r0 = st)
    (hw : stR st ∈ s₀.wr) (i : Nat) (s : State) (hi : i < 5) (hs : PI H st s₀ i s) :
    WP isa (.block [.dp .add (yr (2 * i)) (yr (2 * i)) (.shifted (yr (2 * i + 1)) .lsl 16),
      .str (yr (2 * i)) .r0 (4 * i)]) s (PI H st s₀ (i + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hne : yr (2 * i) ≠ yr (2 * i + 1) := fun e => absurd (yr_inj _ (by omega_using [hi]) _ (by omega_using [hi]) e) (by omega_using [])
  refine wp_add (op2_lsl (by decide)) fun s1 u1 => ?_
  have hv : (s1.gpr (yr (2 * i))).toNat = H (2 * i) + 2 ^ 16 * H (2 * i + 1) := by
    have a := hs.cols (2 * i) (by omega_using [hi]) (Nat.le_refl _)
    have b := hs.cols (2 * i + 1) (by omega_using [hi]) (by omega_using [])
    have := hH (2 * i) (by omega_using [hi]); have := hH (2 * i + 1) (by omega_using [hi])
    rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, a, b]; omega), toNat_shl, a, b]
    omega_using [b, this]
  refine wp_str (off := 4 * i) (a := State.addr st + BitVec.ofNat 64 (4 * i)) (by omega_using [hi]) (by rw [u1.other _ (yr_ne' (2 * i) (by omega_using [hi])).1.symm, hs0]; exact ea hfit (off := 4 * i) (by omega_using [hi]))
    (by rw [u1.wr]; exact outSt hsw (off := 4 * i) (n := 4) (by omega_using [hi])) fun s2 u2 => WP.block_nil ⟨fun i' hi' => ?_, ?_, ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega_using [hi, h']) (by omega_using [hi]) (by omega_using [h']), u1.mem]; exact hs.mem i' h'
    · rw [Mem.readW_writeW_self32]; exact hv
  · intro k hk hk'
    rw [u2.gpr, u1.other _ (fun e => absurd (yr_inj _ hk _ (by omega_using [hi]) e) (by omega_using [hk']))]
    exact hs.cols k hk (by omega_using [hk'])
  · refine hs.keeps.trans ⟨fun r hr => ?_, ?_, u2.rd.trans u1.rd, u2.wr.trans u1.wr, u2.sp.trans u1.sp⟩
    · rw [u2.gpr, u1.other _ (fun e => hr (by rw [e]; exact yr_work _ (by omega_using [hi])))]
    · rw [u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (contains_off (by omega_using [hi]) (by omega_using [hi]))

theorem pack_ok {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (hc : Cols H s) :
    WP isa (.block pack) s fun s' => HMem H s'.mem (State.addr st) ∧
      KeepsF work [accR (State.addr st)] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (PI H st s) (fun i s' hi hs => pack_step hfit hH h0 hw i s'
    hi hs) 5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), fun k hk _ => hc k hk,
      (Keeps.refl _ _).keepsF _⟩) fun s' h => ⟨h.mem, h.keeps⟩

end

theorem accR_disjoint (B : Addr) {a n : Nat} (ha : 20 ≤ a) (hn : a + n ≤ 128) :
    (⟨B + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (accR B) :=
  Offset.disjoint_base B (by omega_using [ha]) (by omega_using [hn])

theorem rval_frame {m m' : Mem} {B : Addr} (hf : Frame [accR B] m m') {i : Nat} (hi : i < 10) :
    rval m' B i = rval m B i := by
  have hro := rOff_lt i hi
  have h88 : 88 ≤ rOff i := by have : ∀ i < 10, 88 ≤ rOff i := by decide +kernel
                               exact this i hi
  simp only [rval]
  split
  · congr 1
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact accR_disjoint B (a := rOff i) (n := 1) (by omega_using [hro, h88]) (by omega_using [hro, h88]) _
      (Region.contains_self _ _ |>.byte (by simp only [BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.lt_add_one])) hc
  · rw [hf.readW (r := ⟨B + BitVec.ofNat 64 (rOff i), 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]; exact accR_disjoint B (by omega_using [hro, h88]) (by omega_using [hro])) (by decide)]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The columns after adding a block: `D` plus the limbs of the block and, if `pad`, `2¹²⁸`. -/
def addE (D : Nat → Nat) (w : Nat → Nat) (pad : Bool) : Nat → Nat :=
  fun k => D k + mlimb (w 0) (w 1) (w 2) (w 3) k + if k = 9 ∧ pad = true then 2 ^ 11 else 0

omit hfit in
theorem val_add (f g : Nat → Nat) : val (fun k => f k + g k) = val f + val g := by
  simp only [val]; omega

omit hfit in
theorem val_addE (D w : Nat → Nat) (pad : Bool) :
    val (addE D w pad) = val D + val (mlimb (w 0) (w 1) (w 2) (w 3)) + if pad then 2 ^ 128 else 0 := by
  unfold addE
  rw [val_add (fun k => D k + mlimb (w 0) (w 1) (w 2) (w 3) k)
    (fun k => if k = 9 ∧ pad = true then 2 ^ 11 else 0), val_add]
  cases pad <;> rfl

theorem absorb_ok (pad : Bool) {R D : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13)
    (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hRm : ∀ i < 10, rval s.mem (State.addr st) i = R i) (hc : ColsD D (State.addr st) s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorb pad)) s fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
      val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
      KeepsF work [accR (State.addr st)] s s' := by
  have hw4 : ∀ i, (word s i).toNat < 2 ^ 32 := fun i => (word s i).isLt
  have hEb : ∀ k < 10, addE D (fun i => (word s i).toNat) pad k < 2 ^ 32 - 2 ^ 19 := fun k hk => by
    have := hD k hk; have := mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    simp only [addE]; split <;> omega
  rw [absorb]
  simp only [List.append_assoc]
  refine WP.append (addWords_ok hin) fun s1 ⟨hc1, hr2, k1⟩ => ?_
  have e1 : ∀ k < 9, (s1.gpr (yr k)).toNat = addE D (fun i => (word s i).toNat) pad k := fun k hk => by
    have := hD k (by omega_using [hk]); have := mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    rw [hc1 k hk, toNat_add_lt (by rw [wsum_toNat _ hk, hc.1 k hk]; omega), wsum_toNat _ hk, hc.1 k hk]
    simp only [addE, iteF (show ¬(k = 9 ∧ pad = true) by omega_using [hk]), Nat.add_zero]
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  have hsw1 : stR st ∈ s1.wr := by rw [k1.wr]; exact hw
  -- `addTop pad`: column 9 into `r1`.
  have top : WP isa (.block (addTop pad ++ (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off]))))) s1
      (fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
        val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
        KeepsF work [accR (State.addr st)] s s') := by
    -- After `addTop`: the columns `E` in registers, the memory of `s`.
    have rest : ∀ s2 : State, Cols (addE D (fun i => (word s i).toNat) pad) s2 →
        KeepsF work [accR (State.addr st)] s s2 → s2.mem = s.mem →
        WP isa (.block (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off])))) s2
          (fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
            val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
            KeepsF work [accR (State.addr st)] s s') := by
      intro s2 hc2 k2 hm2
      have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), h0]
      obtain ⟨hv, -, hf0, hf1, hfj⟩ := fold_facts _ hEb
      have hH : ∀ k < 10, fold (addE D (fun i => (word s i).toNat) pad) k ≤ Hb := fun k hk => by
        simp only [Hb]
        rcases Nat.lt_or_ge k 2 with h | h
        · rcases (by omega_using [hk, h] : k = 0 ∨ k = 1) with rfl | rfl <;> omega_using [hf0, hf1]
        · have := hfj k h hk; omega_using [this]
      have hH16 : ∀ k < 10, fold (addE D (fun i => (word s i).toNat) pad) k < 2 ^ 16 := fun k hk => by
        have := hH k hk; simp only [Hb] at this; omega_using [this]
      refine WP.append (carryFold_ok hEb hc2) fun s3 ⟨hc3, _, k3⟩ => ?_
      have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), hs20]
      have hw3 : stR st ∈ s3.wr := by rw [k3.wr, k2.wr]; exact hw
      refine WP.append (pack_ok hfit hH16 hs30 hw3 hc3) fun s4 ⟨hHm, k4⟩ => ?_
      have hs40 : s4.gpr .r0 = st := by rw [k4.gpr _ (by decide), hs30]
      have hw4' : stR st ∈ s4.wr := by rw [k4.wr]; exact hw3
      have hR4 : ∀ i < 10, rval s4.mem (State.addr st) i = R i := fun i hi => by
        rw [rval_frame k4.frame hi, k3.mem, hm2]; exact hRm i hi
      refine WP.append (multiply_ok hfit hH hR hs40 hw4' hR4 hHm) fun s5 ⟨hx5, k5⟩ => ?_
      have hs50 : s5.gpr .r0 = st := by rw [k5.gpr _ (by decide), hs40]
      refine wp_str (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
        (by rw [hs50]; exact ea hfit (off := 16) (by decide))
        (by rw [k5.wr]; exact outSt hw4' (off := 16) (n := 4) (by decide)) fun s6 u6 => WP.block_nil ?_
      refine ⟨col (fold (addE D (fun i => (word s i).toNat) pad)) R, ⟨fun k hk => ?_, ?_⟩,
        fun k hk => col_lt hH hR hk, ?_, ?_⟩
      · rw [u6.gpr, yr_eq_xr k hk]; exact hx5 k (by omega_using [hk])
      · rw [u6.mem, Mem.readW_writeW_self32]; exact hx5 9 (by decide)
      · rw [val_col, Nat.mul_mod, hv, ← Nat.mul_mod]
        refine congrArg (· % P) (congrArg (· * val R) ?_)
        have hm := val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)
        rw [val_addE, hm, msgVal]
      · have k6 : KeepsF work [accR (State.addr st)] s5 s6 := by
          refine ⟨fun r _ => by rw [u6.gpr], ?_, u6.rd, u6.wr, u6.sp⟩
          rw [u6.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))
        exact k2.trans (((k3.keepsF _).mono (by simp only [cregs, yregs, List.mem_cons, List.not_mem_nil, or_false, work, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self])).trans (k4.trans
          ((k5.keepsF _).trans k6)))
    rw [addTop]
    simp only [List.append_assoc, List.cons_append]
    refine wp_ldr (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
      (by rw [hs10]; exact ea hfit (off := 16) (by decide)) (inSt hsw1 (off := 16) (n := 4) (by decide))
      fun s2 u2 => wp_add (op2_lsr (by decide)) fun s3 u3 => ?_
    have hD9 := hD 9 (by decide)
    have v3 : (s3.gpr .r1).toNat = D 9 + (word s 3).toNat / 2 ^ 21 := by
      have e2 : (s2.gpr .r1).toNat = D 9 := by rw [u2.gpr, k1.mem]; exact hc.2
      rw [u3.gpr, u2.other .r2 (by decide), hr2, toNat_add_lt (by rw [e2, toNat_shr]; have := hw4 3; omega_using [hD9, e2, this]),
        e2, toNat_shr]
    have k3 : KeepsF work [accR (State.addr st)] s s3 :=
      (k1.keepsF _).mono (by simp only [yregs, List.mem_cons, List.not_mem_nil, or_false, work, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self]) |>.trans
        (((u2.keeps (ws := [.r1]) (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))).keepsF _ |>.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, work, forall_eq, reduceCtorEq, or_self]))
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, k1.mem]
    have c3 : ∀ j < 9, (s3.gpr (yr j)).toNat = addE D (fun i => (word s i).toNat) pad j := fun j hj => by
      rw [u3.other _ (yr_ne j hj).2.1, u2.other _ (yr_ne j hj).2.1]; exact e1 j hj
    cases pad
    · simp only [Bool.false_eq_true, ite_false, List.nil_append]
      refine rest s3 (fun j hj => ?_) k3 m3
      rcases Nat.lt_or_ge j 9 with h | h
      · exact c3 j h
      · rw [show j = 9 by omega_using [hj, h], yr9, v3]; simp [addE, mlimb]
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine wp_add (op2_imm (by decide)) fun s4 u4 => rest s4 (fun j hj => ?_)
        (k3.trans ((u4.keeps (ws := [.r1]) (by simp only [List.mem_cons, List.not_mem_nil, or_false])).keepsF _ |>.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, work, forall_eq, reduceCtorEq, or_self]))) (by rw [u4.mem, m3])
      rcases Nat.lt_or_ge j 9 with h | h
      · rw [u4.other _ (yr_ne j h).2.1]; exact c3 j h
      · have e2048 : (2048 : BitVec 32).toNat = 2048 := rfl
        rw [show j = 9 by omega_using [hj, h], yr9, u4.gpr, toNat_add_lt (by rw [v3, e2048]; have := hw4 3; omega_using [hD9, v3]), v3,
          e2048]
        simp [addE, mlimb]
  exact top

end

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Setup`.
section

section

/-!
# Poly1305 on 32-bit ARM: runs of stores and loads

Untrusted: everything here is checked by Lean. A run of stores of registers
(words, or bytes) at distinct offsets from a base register (`stores_ok`),
and a run of loads (`loads_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The store of register `r` at `[b, #o]`: a word, or a byte if `byte`. -/
def storeI (b : Reg) : Reg × Nat × Bool → Instr
  | (r, o, false) => .str r b o
  | (r, o, true) => .strb r b o

/-- The size of a store. -/
def ssize : Bool → Nat
  | false => 4
  | true => 1

/-- The bytes a store writes. -/
def sregion (B : Addr) (x : Reg × Nat × Bool) : Region := ⟨B + BitVec.ofNat 64 x.2.1, ssize x.2.2⟩

/-- What a store leaves in memory: register `r`'s value, or its low byte, at `B + o`. -/
def Stored (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Reg × Nat × Bool → Prop
  | (r, o, false) => m.readW (B + BitVec.ofNat 64 o) 32 = g r
  | (r, o, true) => m (B + BitVec.ofNat 64 o) = (g r).setWidth 8

/-- Two stores' bytes do not overlap. -/
def Apart (x y : Reg × Nat × Bool) : Prop := x.2.1 + ssize x.2.2 ≤ y.2.1 ∨ y.2.1 + ssize y.2.2 ≤ x.2.1

instance (x y : Reg × Nat × Bool) : Decidable (Apart x y) := by unfold Apart; infer_instance

theorem sregion_disjoint (B : Addr) {x y : Reg × Nat × Bool} (h : Apart x y) (hx : x.2.1 < 2 ^ 32)
    (hy : y.2.1 < 2 ^ 32) : (sregion B x).Disjoint (sregion B y) := by
  obtain ⟨_, o, b⟩ := x
  obtain ⟨_, o', b'⟩ := y
  simp only [Apart] at h hx hy
  simp only [sregion]
  cases b <;> cases b' <;> simp only [ssize] at h ⊢ <;> exact Offset.disjoint B h (by omega_using [hx]) (by omega_using [hy])

theorem Stored.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} {x : Reg × Nat × Bool}
    (h : Stored B g m x) {F : List Region} (hf : Frame F m m')
    (hd : ∀ r ∈ F, (sregion B x).Disjoint r) : Stored B g m' x := by
  obtain ⟨r, o, b⟩ := x
  cases b
  · simp only [Stored] at h ⊢
    rw [hf.readW (Region.contains_self _ _) hd (by decide)]; exact h
  · simp only [Stored] at h ⊢
    rw [hf _ fun r' hr' hc => hd r' hr' _ (by simp only [Region.Contains, sregion, ssize, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_add, Std.le_refl]) hc]; exact h

theorem stores_ok (b : Reg) {B : Addr} {bv : BitVec 32} {len : Nat} (hfit : bv.toNat + len ≤ 2 ^ 32)
    (hB : B = State.addr bv) : ∀ (l : List (Reg × Nat × Bool)) (s : State),
    s.gpr b = bv → (⟨B, len⟩ : Region) ∈ s.wr → (∀ x ∈ l, x.2.1 + ssize x.2.2 ≤ len ∧ x.2.1 < 4096) →
    l.Pairwise Apart →
    WP isa (.block (l.map (storeI b))) s fun s' =>
      (∀ x ∈ l, Stored B s.gpr s'.mem x) ∧ Frame (l.map (sregion B)) s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | [], s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | x :: xs, s, hb, hw, hl, hp => by
    obtain ⟨r, o, byte⟩ := x
    have ⟨hlo, ho⟩ := hl _ List.mem_cons_self
    simp only at hlo ho
    have h1s : 1 ≤ ssize byte := by cases byte <;> simp [ssize]
    have ha : State.addr (s.gpr b + BitVec.ofNat 32 o) = B + BitVec.ofNat 64 o := by
      rw [hb, hB]; exact addr_add (by omega_using [hfit, hlo, h1s])
    have hc : (⟨B, len⟩ : Region).Contains (B + BitVec.ofNat 64 o) (ssize byte) :=
      contains_off hlo (by omega_using [ho])
    have hp' := List.pairwise_cons.mp hp
    have rest : ∀ s1 : State, Mupd s s1 (s1.mem) → Stored B s.gpr s1.mem (r, o, byte) →
        Frame [sregion B (r, o, byte)] s.mem s1.mem →
        WP isa (.block (xs.map (storeI b))) s1 fun s' =>
          (∀ x ∈ (r, o, byte) :: xs, Stored B s.gpr s'.mem x) ∧
          Frame (((r, o, byte) :: xs).map (sregion B)) s.mem s'.mem ∧
          s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
      intro s1 u1 hst hf1
      refine WP.mono (stores_ok b hfit hB xs s1 (by rw [u1.gpr, hb]) (by rw [u1.wr]; exact hw)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hp'.2) fun s' ⟨hs', hf', hg', hrd', hwr', hsp'⟩ =>
        ⟨fun y hy => ?_, ?_, hg'.trans u1.gpr, hrd'.trans u1.rd, hwr'.trans u1.wr, hsp'.trans u1.sp⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · refine hst.frame hf' fun q hq => ?_
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
          exact sregion_disjoint B (hp'.1 z hz) (by simp only; omega_using [ho])
            (by have := hl z (List.mem_cons_of_mem _ hz); omega_using [this])
        · rw [← u1.gpr]; exact hs' y hy
      · simp only [List.map_cons]
        refine (hf1.mono fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; simp only [hq, List.mem_cons, List.mem_map, Prod.exists, Bool.exists_bool, true_or]).trans (hf'.mono fun q hq => by simp only [List.mem_cons, hq, or_true])
    cases byte
    · refine wp_str (a := B + BitVec.ofNat 64 o) (by omega_using [ho]) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp, u1.z⟩ ?_ ?_
      · simp only [Stored]; rw [u1.mem, Mem.readW_writeW_self32]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · refine wp_strb (a := B + BitVec.ofNat 64 o) (by omega_using [ho]) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp, u1.z⟩ ?_ ?_
      · simp only [Stored]; rw [u1.mem]
        simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_lt_succ, Nat.div_self, Nat.lt_add_one, ↓reduceIte, Nat.reduceDiv, Nat.reduceMul, Nat.mul_zero, BitVec.setWidth_eq, BitVec.extractLsb'_eq_self]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: saving registers, the limbs of `r`, and loading the accumulator

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-! ## Saving and restoring the callee-saved registers -/

/-- The registers `g` saved at `[56, 88)` of the state at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (56 + 4 * i)) 32 = g (savedReg i)

def saveList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 56 + 4 * i, false)

theorem saveRegs_eq : saveRegs = saveList.map (storeI .r0) := rfl

/-- The saved registers' region. -/
abbrev saveR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 32⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem saveRegs_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block saveRegs) s fun s' => Saved (State.addr st) s.gpr s'.mem ∧
      Frame [saveR (State.addr st)] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [saveRegs_eq]
  refine WP.mono (stores_ok .r0 hfit rfl saveList s h0 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 56 + 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, sub_sub _ (by simp only; omega_using [this]) (by simp only [ssize, Nat.reduceAdd, Nat.reduceLeDiff]; omega_using [this]) (by decide)⟩

theorem restoreRegs_ok {s : State} {g : Reg → BitVec 32} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hs : Saved (State.addr st) g s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide +kernel
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide +kernel
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 (56 + 4 * n)) (by omega_using [hn])
    (by rw [hk.gpr _ (by decide), h0]; exact ea hfit (by omega_using [hn]))
    (by rw [hk.rd, hk.wr]; exact inSt hw (by omega_using [hn])) fun s1 u1 => WP.block_nil ⟨fun i hi => ?_,
      hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

/-! ## The limbs of `r` -/

/-- The key's words at `[24, 40)`, clamped. -/
def cw (m : Mem) (B : Addr) (i : Nat) : BitVec 32 :=
  m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 &&& (if i = 0 then 0x0fffffff else 0x0ffffffc)

/-- The limbs of the clamped `r` of the key in the memory `m` of the state at `B`. -/
def rlimb (m : Mem) (B : Addr) : Nat → Nat :=
  mlimb (cw m B 0).toNat (cw m B 1).toNat (cw m B 2).toNat (cw m B 3).toNat

/-- The region `clampWords` and `setupR` write. -/
abbrev rR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 88, 36⟩

omit hfit in
theorem key_rR (B : Addr) {d : Nat} (hd : d + 4 ≤ 88) :
    (⟨B + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint (rR B) :=
  Offset.disjoint B (Or.inl hd) (by omega_using [hd]) (by decide)

theorem clampWords_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block clampWords) s fun s' =>
      (∀ i < 4, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 = cw s.mem (State.addr st) i) ∧
      KeepsF [.r1, .r2] [rR (State.addr st)] s s' := by
  have hkey : ∀ {m : Mem}, Frame [rR (State.addr st)] s.mem m → ∀ i < 4,
      m.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 =
        s.mem.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 := fun hf i hi =>
    hf.readW (Region.contains_self _ _) (by simpa using key_rR (State.addr st) (d := 24 + 4 * i) (by omega_using [hi]))
      (by decide)
  rw [clampWords]
  simp only [List.cons_append]
  refine wp_movw fun s1 u1 => wp_movt fun s2 u2 => ?_
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 24) (by decide)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), h0]; exact ea hfit (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact inSt hw (by decide)) fun s3 u3 => ?_
  refine wp_and (op2_reg _ _) fun s4 u4 => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 88) (by decide)
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h0]; exact ea hfit (by decide))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact outSt hw (by decide)) fun s5 u5 => ?_
  refine wp_movw fun s6 u6 => wp_movt fun s7 u7 => ?_
  rw [List.nil_append]
  have v0 : s5.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = cw s.mem (State.addr st) 0 := by
    rw [u5.mem, Mem.readW_writeW_self32, u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, u1.gpr,
      u2.mem, u1.mem]
    rfl
  have k7 : KeepsF [.r1, .r2] [rR (State.addr st)] s s7 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u7.other _ hr.2, u6.other _ hr.2, u5.gpr, u4.other _ hr.1, u3.other _ hr.1, u2.other _ hr.2,
        u1.other _ hr.2]
    · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub _ (by decide) (by decide)
        (by decide))
    · rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  have m2 : s7.gpr .r2 = 0x0ffffffc := by rw [u7.gpr, u6.gpr]; rfl
  have m7 : s7.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = cw s.mem (State.addr st) 0 := by
    rw [u7.mem, u6.mem]; exact v0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n + 1, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 =
      cw s.mem (State.addr st) i) ∧ s'.gpr .r2 = 0x0ffffffc ∧ KeepsF [.r1, .r2] [rR (State.addr st)] s s')
    (fun n s' hn ⟨hl, hr2, hk⟩ => ?_) 3 (Nat.le_refl _) s7 ⟨fun i hi => by rw [show i = 0 by omega_using [hi]]; exact m7,
      m2, k7⟩) fun s' ⟨hl, _, hk⟩ => ⟨hl, hk⟩
  have hs0 : s'.gpr .r0 = st := by rw [hk.gpr _ (by decide), h0]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 (24 + 4 * (n + 1))) (by omega_using [hn])
    (by rw [hs0, show 28 + 4 * n = 24 + 4 * (n + 1) by omega_using []]; exact ea hfit (by omega_using [hn]))
    (by rw [hk.rd, hk.wr]; exact inSt hw (by omega_using [hn])) fun s1 u1 => ?_
  refine wp_and (op2_reg _ _) fun s2 u2 => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 (88 + 4 * (n + 1))) (by omega_using [hn])
    (by rw [u2.other _ (by decide), u1.other _ (by decide), hs0,
      show 92 + 4 * n = 88 + 4 * (n + 1) by omega_using []]; exact ea hfit (by omega_using [hn]))
    (by rw [u2.wr, u1.wr, hk.wr]; exact outSt hw (by omega_using [hn])) fun s3 u3 => WP.block_nil ⟨fun i hi => ?_, ?_, ?_⟩
  · rw [u3.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega_using [hn, h']) (by omega_using [hn]) (by omega_using [h']), u2.mem, u1.mem]; exact hl i h'
    · rw [Mem.readW_writeW_self32, u2.gpr, u1.gpr, u1.other _ (by decide), hr2, hkey hk.frame _ (by omega_using [hn]),
        cw, iteF (by omega_using [hn])]
  · rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), hr2]
  · refine hk.trans ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u3.gpr, u2.other _ hr.1, u1.other _ hr.1]
    · rw [u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub _ (by omega_using [hn]) (by omega_using [hn])
        (by decide))
    · rw [u3.rd, u2.rd, u1.rd]
    · rw [u3.wr, u2.wr, u1.wr]
    · rw [u3.sp, u2.sp, u1.sp]

omit hfit in
theorem zeroY_ok {s : State} :
    WP isa (.block zeroY) s fun s' => (∀ k < 9, s'.gpr (yr k) = 0) ∧ Keeps yregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, s'.gpr (yr k) = 0) ∧ Keeps yregs s s')
    (fun n s' hn ⟨hz, hk⟩ => wp_mov (op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (yr_yregs n hn))⟩) 9 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (yr_inj _ (by omega_using [hn, h']) _ (by omega_using [hn]) e) (by omega_using [h']))]; exact hz k h'
  · rw [u1.gpr]

/-- The stores of the limbs of `r` in `setupR`. -/
def rList : List (Reg × Nat × Bool) :=
  [(.r3, 88, false), (.r4, 92, false), (.r5, 96, false), (.r6, 100, false), (.r7, 120, true),
   (.r8, 104, false), (.r9, 108, false), (.r10, 112, false), (.r11, 116, false), (.r1, 121, true)]

omit hfit in
theorem setupR_eq : setupR = clampWords ++ zeroY ++ ([.dp .add .r1 .r0 (.imm 88)] : List Instr) ++ addWords ++
    ([.mov .r1 (.shifted .r2 .lsr 21)] : List Instr) ++ rList.map (storeI .r0) := rfl

omit hfit in
theorem cw_lt (m : Mem) (B : Addr) (i : Nat) : (cw m B i).toNat < 2 ^ 28 := by
  simp only [cw, BitVec.toNat_and]
  split
  · exact and_lt (by decide)
  · exact and_lt (by decide)

omit hfit in
theorem cw2_even (m : Mem) (B : Addr) : (cw m B 2).toNat % 2 = 0 := by
  simp only [cw, BitVec.toNat_and, show (2 : Nat) ≠ 0 by decide, ite_false]
  exact and_fffffffc_mod _

omit hfit in
theorem rlimb_lt (m : Mem) (B : Addr) (i : Nat) : rlimb m B i < 2 ^ 13 :=
  mlimb_lt (by have := cw_lt m B 0; omega_using [this]) (by have := cw_lt m B 1; omega_using [this])
    (by have := cw_lt m B 2; omega_using [this]) (by have := cw_lt m B 3; omega_using [this]) i

theorem setupR_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block setupR) s fun s' => (∀ i < 10, rval s'.mem (State.addr st) i = rlimb s.mem (State.addr st) i) ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) [rR (State.addr st)] s s' := by
  rw [setupR_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (clampWords_ok hfit h0 hw) fun s1 ⟨hm1, k1⟩ => ?_
  refine WP.append zeroY_ok fun s2 ⟨hz2, k2⟩ => ?_
  have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), h0]
  refine wp_add (op2_imm (by decide)) fun s3 u3 => ?_
  have hs3 : s3.gpr .r1 = st + 88 := by rw [u3.gpr, hs20]
  have hw3 : stR st ∈ s3.wr := by rw [u3.wr, k2.wr, k1.wr]; exact hw
  have hwd : ∀ i < 4, State.addr (s3.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (88 + 4 * i) := fun i hi => by
    rw [hs3, BitVec.add_assoc, show (88 : BitVec 32) = BitVec.ofNat 32 88 from rfl, ← BitVec.ofNat_add]
    exact ea hfit (by omega_using [hi])
  refine WP.append (addWords_ok fun i hi => by rw [hwd i hi]; exact inSt hw3 (by omega_using [hi]))
    fun s4 ⟨hc4, hr4, k4⟩ => ?_
  have hword : ∀ i < 4, word s3 i = cw s.mem (State.addr st) i := fun i hi => by
    simp only [word]; rw [hwd i hi, u3.mem, k2.mem]; exact hm1 i hi
  have e4 : ∀ k < 9, (s4.gpr (yr k)).toNat = rlimb s.mem (State.addr st) k := fun k hk => by
    rw [hc4 k hk, u3.other _ (yr_ne k hk).2.1, hz2 k hk, zadd, wsum_toNat _ hk, hword 0 (by decide),
      hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
    rfl
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have e5 : (s5.gpr .r1).toNat = rlimb s.mem (State.addr st) 9 := by
    rw [u5.gpr, toNat_shr, hr4, hword 3 (by decide)]; rfl
  have hs50 : s5.gpr .r0 = st := by rw [u5.other _ (by decide), k4.gpr _ (by decide), u3.other _ (by decide), hs20]
  have hw5 : stR st ∈ s5.wr := by rw [u5.wr, k4.wr]; exact hw3
  refine WP.mono (stores_ok .r0 hfit rfl rList s5 hs50 hw5 (by decide) (by decide))
    fun s6 ⟨hs6, hf6, hg6, hrd6, hwr6, hsp6⟩ => ⟨fun i hi => ?_, ?_⟩
  · have hr : ∀ k < 9, (s5.gpr (yr k)).toNat = rlimb s.mem (State.addr st) k := fun k hk => by
      rw [u5.other _ (yr_ne k hk).2.1]; exact e4 k hk
    have b4 : rlimb s.mem (State.addr st) 4 < 2 ^ 8 := by
      have := cw_lt s.mem (State.addr st) 1; have := cw2_even s.mem (State.addr st)
      simp only [rlimb, mlimb]; omega
    have b9 : rlimb s.mem (State.addr st) 9 < 2 ^ 8 := by
      have := cw_lt s.mem (State.addr st) 3
      simp only [rlimb, mlimb]; omega_using [this]
    have w : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, false) ∈ rList → (s5.gpr r).toNat = rlimb s.mem (State.addr st) k →
        (s6.mem.readW (State.addr st + BitVec.ofNat 64 o) 32).toNat = rlimb s.mem (State.addr st) k :=
      fun r o k hm hv => by have := hs6 _ hm; simp only [Stored] at this; rw [this, hv]
    have b : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, true) ∈ rList → (s5.gpr r).toNat = rlimb s.mem (State.addr st) k →
        rlimb s.mem (State.addr st) k < 2 ^ 8 →
        (s6.mem (State.addr st + BitVec.ofNat 64 o)).toNat = rlimb s.mem (State.addr st) k :=
      fun r o k hm hv hb => by
        have := hs6 _ hm; simp only [Stored] at this
        rw [this, BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt hb]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega_using [hi]
    all_goals simp only [rval, rOff, Nat.reduceEqDiff, or_self, or_false, false_or, ite_true,
      ite_false]
    · exact w .r3 88 0 (by decide) (hr 0 (by decide))
    · exact w .r4 92 1 (by decide) (hr 1 (by decide))
    · exact w .r5 96 2 (by decide) (hr 2 (by decide))
    · exact w .r6 100 3 (by decide) (hr 3 (by decide))
    · exact b .r7 120 4 (by decide) (hr 4 (by decide)) b4
    · exact w .r8 104 5 (by decide) (hr 5 (by decide))
    · exact w .r9 108 6 (by decide) (hr 6 (by decide))
    · exact w .r10 112 7 (by decide) (hr 7 (by decide))
    · exact w .r11 116 8 (by decide) (hr 8 (by decide))
    · exact b .r1 121 9 (by decide) e5 b9
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [hg6, u5.other _ hr.1, k4.gpr _ (by simp only [List.mem_cons, hr.2.1, hr.2.2.1, hr.2.2.2, or_self, not_false_eq_true]), u3.other _ hr.1,
        k2.gpr _ hr.2.2.2, k1.gpr _ (by simp only [List.mem_cons, hr.1, hr.2.1, List.not_mem_nil, or_self, not_false_eq_true])]
    · have e : s5.mem = s1.mem := by rw [u5.mem, k4.mem, u3.mem, k2.mem]
      rw [e] at hf6
      refine k1.frame.trans (hf6.sub fun r hr => ?_)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hb : ∀ x ∈ rList, 88 ≤ x.2.1 ∧ x.2.1 + ssize x.2.2 ≤ 124 := by decide
      have := hb x hx
      exact ⟨_, List.mem_singleton_self _, sub_sub _ this.1 (by omega_using [this]) (by decide)⟩
    · rw [hrd6, u5.rd, k4.rd, u3.rd, k2.rd, k1.rd]
    · rw [hwr6, u5.wr, k4.wr, u3.wr, k2.wr, k1.wr]
    · rw [hsp6, u5.sp, k4.sp, u3.sp, k2.sp, k1.sp]

/-! ## Loading the accumulator -/

/-- Word `i` of the state at `B`. -/
def hwd (m : Mem) (B : Addr) (i : Nat) : Nat := (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat

/-- The columns `loadAcc` makes of the accumulator stored in the state at `B`. -/
def accD (m : Mem) (B : Addr) : Nat → Nat := fun k =>
  if k = 9 then hwd m B 3 / 2 ^ 21 + hwd m B 4 % 4 * 2 ^ 11
  else mlimb (hwd m B 0) (hwd m B 1) (hwd m B 2) (hwd m B 3) k

omit hfit in
theorem accD_lt (m : Mem) (B : Addr) (k : Nat) : accD m B k < 2 ^ 13 := by
  have h3 : hwd m B 3 < 2 ^ 32 := BitVec.isLt _
  simp only [accD]
  split
  · omega_using [h3]
  · exact mlimb_lt (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) h3 k

omit hfit in
theorem val_accD (m : Mem) (B : Addr) :
    val (accD m B) = hwd m B 0 + 2 ^ 32 * hwd m B 1 + 2 ^ 64 * hwd m B 2 + 2 ^ 96 * hwd m B 3 +
      2 ^ 128 * (hwd m B 4 % 4) := by
  have hv := val_mlimb (w0 := hwd m B 0) (w1 := hwd m B 1) (w2 := hwd m B 2) (w3 := hwd m B 3)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  simp only [val, accD, Nat.reduceEqDiff, ite_true, ite_false] at hv ⊢
  simp only [mlimb] at hv ⊢
  omega_using [hv]

theorem loadAcc_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block loadAcc) s fun s' => ColsD (accD s.mem (State.addr st)) (State.addr st) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) [accR (State.addr st)] s s' := by
  rw [loadAcc]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append zeroY_ok fun s1 ⟨hz1, k1⟩ => ?_
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  have hw2 : stR st ∈ s2.wr := by rw [u2.wr, k1.wr]; exact hw
  have hwd' : ∀ i < 4, State.addr (s2.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (4 * i) := fun i hi => by
    rw [u2.gpr, hs10]; exact ea hfit (by omega_using [hi])
  refine WP.append (addWords_ok fun i hi => by rw [hwd' i hi]; exact inSt hw2 (by omega_using [hi]))
    fun s3 ⟨hc3, hr3, k3⟩ => ?_
  have hword : ∀ i < 4, (word s2 i).toNat = hwd s.mem (State.addr st) i := fun i hi => by
    simp only [word]; rw [hwd' i hi, u2.mem, k1.mem]; rfl
  have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), u2.other _ (by decide), hs10]
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide)
    (by rw [u4.other _ (by decide), hs30]; exact ea hfit (off := 16) (by decide))
    (by rw [u4.rd, u4.wr, k3.rd, k3.wr]; exact inSt hw2 (off := 16) (n := 4) (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s6 u6 => wp_add (op2_lsr (by decide)) fun s7 u7 => ?_
  have v7 : (s7.gpr .r1).toNat = accD s.mem (State.addr st) 9 := by
    have e4 : (s4.gpr .r1).toNat = hwd s.mem (State.addr st) 3 / 2 ^ 21 := by
      rw [u4.gpr, toNat_shr, hr3, hword 3 (by decide)]
    have e6 : (s6.gpr .r2).toNat = hwd s.mem (State.addr st) 4 * 2 ^ 30 % 2 ^ 32 := by
      rw [u6.gpr, u5.gpr, toNat_shl, u4.mem, k3.mem, u2.mem, k1.mem]; rfl
    have h3 : hwd s.mem (State.addr st) 3 < 2 ^ 32 := BitVec.isLt _
    rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide),
      toNat_add_lt (by rw [e4, toNat_shr, e6]; omega_using [e6, h3]), e4, toNat_shr, e6]
    simp only [accD, ite_true]
    omega_using [e6]
  have hs70 : s7.gpr .r0 = st := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      hs30]
  refine wp_str (a := State.addr st + BitVec.ofNat 64 16) (by decide)
    (by rw [hs70]; exact ea hfit (off := 16) (by decide))
    (by rw [u7.wr, u6.wr, u5.wr, u4.wr, k3.wr]; exact outSt hw2 (off := 16) (n := 4) (by decide))
    fun s8 u8 => WP.block_nil ⟨⟨fun k hk => ?_, ?_⟩, ?_⟩
  · have hne := yr_ne k hk
    rw [u8.gpr, u7.other _ hne.2.1, u6.other _ hne.2.2.1, u5.other _ hne.2.2.1, u4.other _ hne.2.1, hc3 k hk,
      u2.other _ hne.2.1, hz1 k hk, zadd, wsum_toNat _ hk, hword 0 (by decide), hword 1 (by decide),
      hword 2 (by decide), hword 3 (by decide)]
    simp only [accD, iteF (show k ≠ 9 by omega_using [hk])]
  · rw [u8.mem, Mem.readW_writeW_self32]; exact v7
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [u8.gpr, u7.other _ hr.1, u6.other _ hr.2.1, u5.other _ hr.2.1, u4.other _ hr.1,
        k3.gpr _ (by simp only [List.mem_cons, hr.2.1, hr.2.2.1, hr.2.2.2, or_self, not_false_eq_true]), u2.other _ hr.1, k1.gpr _ hr.2.2.2]
    · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, k3.mem, u2.mem, k1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))
    · rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, k3.rd, u2.rd, k1.rd]
    · rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, k3.wr, u2.wr, k1.wr]
    · rw [u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, k3.sp, u2.sp, k1.sp]

end

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Bytes`.
section

/-!
# Poly1305 on 32-bit ARM: bytes and words in memory

Untrusted: everything here is checked by Lean. Byte strings in memory as
32-bit little-endian words (`bytesAt_eq_of_words`, `leNum_bytesAt_words`),
the clamped `r` of a stored key as limbs (`val_rlimb`), and regions of the
state.
-/

open VG.PowLit

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let key : Region := ⟨State.addr (s.gpr .r1), 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) (bytesAt s.mem (State.addr (s.gpr .r1)) 32) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem (State.addr (s.gpr .r0)) key msg →
    Repr s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (s.gpr .r1)) (16 * (s.gpr .r2).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, scratch: *mut
    [u64; 16])`:
`state` in `r0`, `count` in `r2:r3`, and `data`, `len` and `scratch` the stack
arguments 0, 1 and 2. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    countArm s = BitVec.ofNat 64 msg.length →
    Buffered s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], scratch: *mut [u64;
    16])`:
`state` in `r0`, `count` in `r2:r3`, and `out` and `scratch` the stack
arguments 0 and 1. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    countArm s = BitVec.ofNat 64 msg.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 16 = mac key msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-! ## Words -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Two byte strings are equal if their words are. -/
theorem bytesAt_eq_of_words {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ j < n, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = m'.readW (q + BitVec.ofNat 64 (4 * j)) 32) :
    bytesAt m p (4 * n) = bytesAt m' q (4 * n) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) :=
    fun a => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e p, e q, Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), Mem.readW_byte m' _ (Nat.mod_lt _ (by decide)),
    h _ (by omega)]

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]
  simp only [Nat.reduceMul, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- A byte string as little-endian words. -/
theorem leNum_bytesAt_words (m : Mem) (p : Addr) : ∀ n,
    leNum (bytesAt m p (4 * n)) = rsum (fun j => 2 ^ (32 * j) * (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).toNat) n
  | 0 => by simp only [bytesAt, Nat.mul_zero, List.range_zero, List.map_nil, leNum, rsum]
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, Poly1305.bytesAt_add, Poly1305.leNum_append,
      Poly1305.length_bytesAt, leNum_bytesAt_4, leNum_bytesAt_words m p n, rsum,
      show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by rw [Nat.pow_mul, Nat.pow_mul]]

theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat := by
  rw [show 16 = 4 * 4 from rfl, leNum_bytesAt_words]
  simp only [rsum, Nat.reduceMul]
  omega

theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat +
      2 ^ 128 * (m.readW (p + BitVec.ofNat 64 16) 32).toNat +
      2 ^ 160 * (m.readW (p + BitVec.ofNat 64 20) 32).toNat := by
  rw [show 24 = 4 * 6 from rfl, leNum_bytesAt_words]
  simp only [rsum, Nat.reduceMul]
  omega

/-! ## The stored key -/

theorem off_add (B : Addr) (a d : Nat) :
    B + BitVec.ofNat 64 a + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (a + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem take_bytesAt (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m p n).take k = bytesAt m p k := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_bytesAt (m : Mem) (p : Addr) (k n : Nat) :
    (bytesAt m p (k + n)).drop k = bytesAt m (p + BitVec.ofNat 64 k) n := by
  rw [Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _)]

/-- The number of the key's first 16 bytes, as four words at `[24, 40)` of the state. -/
theorem leNum_r (m : Mem) (B : Addr) :
    leNum (bytesAt m (B + 24) 16) = (m.readW (B + BitVec.ofNat 64 24) 32).toNat +
      2 ^ 32 * (m.readW (B + BitVec.ofNat 64 28) 32).toNat +
      2 ^ 64 * (m.readW (B + BitVec.ofNat 64 32) 32).toNat +
      2 ^ 96 * (m.readW (B + BitVec.ofNat 64 36) 32).toNat := by
  rw [leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add, off_add, off_add, off_add]

theorem val_rlimb (m : Mem) (B : Addr) :
    val (rlimb m B) = clamp (leNum (bytesAt m (B + 24) 16)) := by
  have hc : ∀ i, (cw m B i).toNat < 2 ^ 32 := fun i => (cw m B i).isLt
  rw [rlimb, val_mlimb (hc 0) (hc 1) (hc 2) (hc 3), leNum_r,
    clamp_words (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)]
  simp only [cw, BitVec.toNat_and, Nat.mul_zero, Nat.add_zero, show (1 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide, ite_true, ite_false]
  rfl

theorem rlimb_frame {m m' : Mem} {B : Addr} (h : ∀ i < 4,
    m'.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32) :
    rlimb m' B = rlimb m B := by
  simp only [rlimb, cw, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-! ## Regions of the state -/

theorem sub_base (p : Addr) {a len len' : Nat} (h : a + len ≤ len') (_h' : len' < 2 ^ 64) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, len'⟩ :=
  Offset.sub_base p h

theorem contains_base (p : Addr) {d n len : Nat} (h : d + n ≤ len) (h' : len < 2 ^ 32) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  contains_off h (by omega)

/-- A region inside `[B + a, B + a + la)` is disjoint from one outside it. -/
theorem disjoint_of_sub {r₁ r₂ r₁' r₂' : Region} (h : r₁'.Disjoint r₂') (h₁ : Region.Sub r₁ r₁')
    (h₂ : Region.Sub r₂ r₂') : r₁.Disjoint r₂ :=
  (h.sub_left h₁).sub_right h₂

end VG.Proof.Poly1305.Arm

end
