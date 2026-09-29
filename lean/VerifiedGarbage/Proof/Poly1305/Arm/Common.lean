import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset

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
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-! ## Limbs -/

/-- The number whose limbs are `f 0, …, f 9`. -/
def val (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 13 * f 1 + 2 ^ 26 * f 2 + 2 ^ 39 * f 3 + 2 ^ 52 * f 4 + 2 ^ 65 * f 5 + 2 ^ 78 * f 6 +
    2 ^ 91 * f 7 + 2 ^ 104 * f 8 + 2 ^ 117 * f 9

theorem val_congr {f g : Nat → Nat} (h : ∀ k < 10, f k = g k) : val f = val g := by
  simp only [val, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega)]

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
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · exact Nat.le_of_eq (congrArg (rsum f) (by omega))

theorem rsum_const (c : Nat) : ∀ n, rsum (fun _ => c) n = n * c
  | 0 => by simp [rsum]
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
  simp [psum, rsum]

theorem psum_row (h r : Nat → Nat) (j k : Nat) :
    psum h r j 10 k = psum h r (j + 1) 0 k := by
  simp only [psum, rsum, Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.mod_lt _ (by omega)))]

theorem psum_ten (h r : Nat → Nat) (k : Nat) : psum h r 10 0 k = col h r k := by
  simp [psum, col]

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
    have e1 : ((i + j) % 10 + 10 - j) % 10 = i := by omega
    rw [e1, ite_eq_left_of_eq_true _ _ (eq_true (show i < i + 1 by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < i by omega))]
    by_cases hij : i + j < 10
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true (show j ≤ (i + j) % 10 by omega)),
        show (i + j) % 10 - j = i by omega]; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j ≤ (i + j) % 10 by omega)),
        show (i + j) % 10 + 10 - j = i by omega, Nat.mul_left_comm, Nat.mul_assoc]; omega
  · have e' : ((k + 10 - j) % 10 < i + 1) = ((k + 10 - j) % 10 < i) := by
      apply propext; omega
    simp only [psum, e', e, ite_false]

theorem psum_le_col (h r : Nat → Nat) {j n k : Nat} (hj : j < 10) :
    psum h r j n k ≤ col h r k := by
  simp only [psum, col]
  have : rsum (fun j' => h j' * coef r k j') j + h j * coef r k j ≤
      rsum (fun j' => h j' * coef r k j') 10 :=
    rsum_mono (fun j' => h j' * coef r k j') (show j + 1 ≤ 10 by omega)
  split <;> omega

theorem rsum_le_of_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j ≤ g j) → rsum f n ≤ rsum g n
  | 0, _ => (Nat.le_refl _)
  | n + 1, h => Nat.add_le_add (rsum_le_of_lt n fun j hj => h j (by omega)) (h n (by omega))

/-- A bound on every column. -/
theorem col_le {h r : Nat → Nat} {H R : Nat} (hh : ∀ j < 10, h j ≤ H) (hr : ∀ i < 10, r i ≤ R)
    {k : Nat} (hk : k < 10) : col h r k ≤ 10 * (H * (5 * R)) := by
  have : ∀ j < 10, h j * coef r k j ≤ H * (5 * R) := fun j hj => by
    apply Nat.mul_le_mul (hh j hj)
    simp only [coef]; split
    · have := hr (k - j) (by omega); omega
    · have := hr (k + 10 - j) (by omega); omega
  have := rsum_le_of_lt 10 this
  rw [rsum_const] at this
  exact this

theorem P_eq : P = 2 ^ 130 - 5 := rfl

/-! ## The columns of a product, as a number -/

theorem rsum_add (f g : Nat → Nat) : ∀ n, rsum (fun j => f j + g j) n = rsum f n + rsum g n
  | 0 => rfl
  | n + 1 => by simp only [rsum, rsum_add f g n]; omega

theorem rsum_mul (c : Nat) (f : Nat → Nat) : ∀ n, c * rsum f n = rsum (fun j => c * f j) n
  | 0 => rfl
  | n + 1 => by rw [rsum, rsum, Nat.mul_add, rsum_mul c f n]

theorem rsum_congr {f g : Nat → Nat} (h : ∀ j, f j = g j) : ∀ n, rsum f n = rsum g n
  | 0 => rfl
  | n + 1 => by rw [rsum, rsum, rsum_congr h n, h n]

theorem rsum_congr_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j = g j) → rsum f n = rsum g n
  | 0, _ => rfl
  | n + 1, h => by rw [rsum, rsum, rsum_congr_lt n (fun j hj => h j (by omega)), h n (by omega)]

theorem modP_of_eq {X V K : Nat} (h : X + 5 * K = V + 2 ^ 130 * K) : V % P = X % P := by
  have : X = V + P * K := by rw [P_eq]; omega
  rw [this, Nat.add_mul_mod_self_left]

theorem rsum_comm (f : Nat → Nat → Nat) (m : Nat) : ∀ n,
    rsum (fun k => rsum (fun j => f k j) m) n = rsum (fun j => rsum (fun k => f k j) n) m
  | 0 => by
    induction m with
    | zero => rfl
    | succ m ih => simp only [rsum] at ih ⊢; omega
  | n + 1 => by
    rw [rsum, rsum_comm f m n, ← rsum_add]; rfl

theorem val_eq (f : Nat → Nat) : val f = rsum (fun k => 2 ^ (13 * k) * f k) 10 := by
  simp only [val, rsum]; omega

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
  all_goals simp [val, cstep]; omega

/-- The carries from columns `a`, …, `a + n - 1`, in order. -/
def carryN (f : Nat → Nat) (a : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => cstep (carryN f a n) (n + a)

theorem val_carryN (f : Nat → Nat) (a : Nat) : ∀ n, n + a ≤ 9 → val (carryN f a n) = val f
  | 0, _ => rfl
  | n + 1, h => by rw [carryN, val_cstep _ (by omega), val_carryN f a n (by omega)]

theorem carryN_above (f : Nat → Nat) (a : Nat) : ∀ n j, n + a < j → carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [carryN, cstep, show j ≠ n + a by omega, show j ≠ n + a + 1 by omega, ite_false]
    exact carryN_above f a n j (by omega)

theorem carryN_below (f : Nat → Nat) (a : Nat) : ∀ n j, j < a → carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [carryN, cstep, show j ≠ n + a by omega, show j ≠ n + a + 1 by omega, ite_false]
    exact carryN_below f a n j h

theorem carryN_lt (f : Nat → Nat) (a : Nat) : ∀ n j, a ≤ j → j < n + a → carryN f a n j < 2 ^ 13
  | 0, _, h₁, h₂ => by omega
  | n + 1, j, h₁, h₂ => by
    simp only [carryN, cstep]
    by_cases e : j = n + a
    · simp only [e, ite_true]; exact Nat.mod_lt _ (by decide)
    · simp only [e, show j ≠ n + a + 1 by omega, ite_false]
      exact carryN_lt f a n j h₁ (by omega)

/-- The column being carried into, if every column is below `2³² - 2¹⁹`. -/
theorem carryN_top (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    ∀ n, n + a ≤ 9 → carryN f a n (n + a) < 2 ^ 32
  | 0, h => by have := hf a (by omega); simp only [carryN, Nat.zero_add]; omega
  | n + 1, h => by
    have ih := carryN_top f a hf n (by omega)
    have e : n + 1 + a = n + a + 1 := by omega
    simp only [carryN, cstep, e, show n + a + 1 ≠ n + a by omega, ite_false, ite_true]
    rw [carryN_above f a n _ (by omega)]
    have := hf (n + a + 1) (by omega)
    have : carryN f a n (n + a) / 2 ^ 13 < 2 ^ 19 := by omega
    omega

/-- The carry step's sum does not overflow. -/
theorem carryN_step_lt (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) (n : Nat)
    (hn : n + a < 9) :
    carryN f a n (n + a + 1) + carryN f a n (n + a) / 2 ^ 13 < 2 ^ 32 := by
  have := carryN_top f a hf n (by omega)
  rw [carryN_above f a n _ (by omega)]
  have := hf (n + a + 1) (by omega)
  omega

/-- After carrying from columns `0, …, 8`, and then adding column 9's bits from 13 up, times 5,
to column 0 and carrying it once more: the result is congruent to the columns modulo `p`
(`p c` less), and its limbs are below `2¹³` but the second, which is below `2¹³ + 2⁹`. -/
def fold (f : Nat → Nat) : Nat → Nat :=
  let F := carryN f 0 9
  cstep (fun j => if j = 0 then F 0 + 5 * (F 9 / 2 ^ 13) else if j = 9 then F 9 % 2 ^ 13 else F j) 0

theorem fold_0 (f : Nat → Nat) :
    fold f 0 = (carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)) % 2 ^ 13 := by
  simp [fold, cstep]

theorem fold_1 (f : Nat → Nat) :
    fold f 1 = carryN f 0 9 1 + (carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)) / 2 ^ 13 := by
  simp [fold, cstep]

theorem fold_9 (f : Nat → Nat) : fold f 9 = carryN f 0 9 9 % 2 ^ 13 := by
  simp [fold, cstep]

theorem fold_mid (f : Nat → Nat) {j : Nat} (h1 : 2 ≤ j) (h2 : j < 9) : fold f j = carryN f 0 9 j := by
  simp only [fold, cstep]
  simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 9 by omega, show 0 + 1 = 1 from rfl,
    ite_false]

theorem fold_facts (f : Nat → Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    val (fold f) % P = val f % P ∧ val (fold f) < 2 ^ 130 + 2 ^ 22 ∧ fold f 0 < 2 ^ 13 ∧
      fold f 1 < 2 ^ 13 + 2 ^ 9 ∧ ∀ j, 2 ≤ j → j < 10 → fold f j < 2 ^ 13 := by
  have hv := val_carryN f 0 9 (by omega)
  have ht := carryN_top f 0 hf 9 (by omega)
  have hl : ∀ j < 9, carryN f 0 9 j < 2 ^ 13 := fun j hj => carryN_lt f 0 9 j (by omega) (by omega)
  simp only [Nat.add_zero] at ht
  have e : ∀ j, fold f j = cstep (fun j => if j = 0 then carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13)
      else if j = 9 then carryN f 0 9 9 % 2 ^ 13 else carryN f 0 9 j) 0 j := fun j => rfl
  generalize carryN f 0 9 = F at hv ht hl e
  have f0 : fold f 0 = (F 0 + 5 * (F 9 / 2 ^ 13)) % 2 ^ 13 := by rw [e]; simp [cstep]
  have f1 : fold f 1 = F 1 + (F 0 + 5 * (F 9 / 2 ^ 13)) / 2 ^ 13 := by rw [e]; simp [cstep]
  have f9 : fold f 9 = F 9 % 2 ^ 13 := by rw [e]; simp [cstep]
  have fj : ∀ j, 2 ≤ j → j < 9 → fold f j = F j := by
    intro j h1 h2
    rw [e]; simp only [cstep]
    simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 9 by omega, show 0 + 1 = 1 from rfl,
      ite_false]
  have l0 := hl 0 (by omega); have l1 := hl 1 (by omega)
  have key : val (fold f) + P * (F 9 / 2 ^ 13) = val F := by
    simp only [val, f0, f1, f9, fj 2 (by omega) (by omega), fj 3 (by omega) (by omega),
      fj 4 (by omega) (by omega), fj 5 (by omega) (by omega), fj 6 (by omega) (by omega),
      fj 7 (by omega) (by omega), fj 8 (by omega) (by omega), P_eq]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hv, ← key, Nat.add_mul_mod_self_left]
  · have l2 := hl 2 (by omega); have l3 := hl 3 (by omega); have l4 := hl 4 (by omega)
    have l5 := hl 5 (by omega); have l6 := hl 6 (by omega); have l7 := hl 7 (by omega)
    have l8 := hl 8 (by omega)
    simp only [val, f0, f1, f9, fj 2 (by omega) (by omega), fj 3 (by omega) (by omega),
      fj 4 (by omega) (by omega), fj 5 (by omega) (by omega), fj 6 (by omega) (by omega),
      fj 7 (by omega) (by omega), fj 8 (by omega) (by omega)]
    omega
  · rw [f0]; exact Nat.mod_lt _ (by decide)
  · rw [f1]; omega
  · intro j h2 h10
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [fj j h2 h]; exact hl j h
    · rw [show j = 9 by omega, f9]; exact Nat.mod_lt _ (by decide)

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
  split <;> omega

theorem val_mlimb {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) :
    val (mlimb w0 w1 w2 w3) = w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 := by
  have e0 : w0 = w0 % 2 ^ 13 + 2 ^ 13 * (w0 % 2 ^ 26 / 2 ^ 13) + 2 ^ 26 * (w0 / 2 ^ 26) := by omega
  have e1 : w1 = w1 % 2 ^ 7 + 2 ^ 7 * (w1 % 2 ^ 20 / 2 ^ 7) + 2 ^ 20 * (w1 / 2 ^ 20) := by omega
  have e2 : w2 = w2 % 2 + 2 * (w2 % 2 ^ 14 / 2) + 2 ^ 14 * (w2 % 2 ^ 27 / 2 ^ 14) +
    2 ^ 27 * (w2 / 2 ^ 27) := by omega
  have e3 : w3 = w3 % 2 ^ 8 + 2 ^ 8 * (w3 % 2 ^ 21 / 2 ^ 8) + 2 ^ 21 * (w3 / 2 ^ 21) := by omega
  simp only [val, mlimb]
  generalize w0 % 2 ^ 13 = a0, w0 % 2 ^ 26 / 2 ^ 13 = a1, w0 / 2 ^ 26 = a2 at *
  generalize w1 % 2 ^ 7 = b0, w1 % 2 ^ 20 / 2 ^ 7 = b1, w1 / 2 ^ 20 = b2 at *
  generalize w2 % 2 = c0, w2 % 2 ^ 14 / 2 = c1, w2 % 2 ^ 27 / 2 ^ 14 = c2, w2 / 2 ^ 27 = c3 at *
  generalize w3 % 2 ^ 8 = d0, w3 % 2 ^ 21 / 2 ^ 8 = d1, w3 / 2 ^ 21 = d2 at *
  subst e0 e1 e2 e3
  omega

/-! ## Words of limbs -/

theorem val_toWords {u : Nat → Nat} (h : ∀ k < 9, u k < 2 ^ 13) :
    val u = (u 0 + 2 ^ 13 * u 1 + 2 ^ 26 * (u 2 % 2 ^ 6)) +
      2 ^ 32 * (u 2 / 2 ^ 6 + 2 ^ 7 * u 3 + 2 ^ 20 * (u 4 % 2 ^ 12)) +
      2 ^ 64 * (u 4 / 2 ^ 12 + 2 * u 5 + 2 ^ 14 * u 6 + 2 ^ 27 * (u 7 % 2 ^ 5)) +
      2 ^ 96 * (u 7 / 2 ^ 5 + 2 ^ 8 * u 8 + 2 ^ 21 * (u 9 % 2 ^ 11)) + 2 ^ 128 * (u 9 / 2 ^ 11) := by
  have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega); have := h 3 (by omega)
  have := h 4 (by omega); have := h 5 (by omega); have := h 6 (by omega); have := h 7 (by omega)
  have := h 8 (by omega)
  simp only [val]
  omega

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
      simp only [spre, rsum]; omega
    rw [e, show 13 * (k + 1) = 13 * k + 13 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (u k)]

theorem chainT_top (u : Nat → Nat) : chainT u 9 / 2 ^ 13 = (val u + 5) / 2 ^ 130 := by
  rw [chainT_eq, Nat.add_comm (u 9)]
  have e : val u + 5 = (spre u 9 + 5) + 2 ^ 117 * u 9 := by
    simp only [val, spre, rsum]; omega
  rw [e, show (130 : Nat) = 117 + 13 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), show 13 * 9 = 117 from rfl]

/-- Limbs below `2¹³` but the top one, which is masked. -/
theorem val_mask_top {g g' : Nat → Nat} (h : ∀ k < 9, g k < 2 ^ 13) (h' : ∀ k < 9, g' k = g k)
    (h9 : g' 9 = g 9 % 2 ^ 13) : val g' = val g % 2 ^ 130 := by
  have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega); have := h 3 (by omega)
  have := h 4 (by omega); have := h 5 (by omega); have := h 6 (by omega); have := h 7 (by omega)
  have := h 8 (by omega)
  have e : val g = val g' + 2 ^ 130 * (g 9 / 2 ^ 13) := by
    simp only [val, h' 0 (by omega), h' 1 (by omega), h' 2 (by omega), h' 3 (by omega),
      h' 4 (by omega), h' 5 (by omega), h' 6 (by omega), h' 7 (by omega), h' 8 (by omega), h9]
    omega
  have hl : val g' < 2 ^ 130 := by
    simp only [val, h' 0 (by omega), h' 1 (by omega), h' 2 (by omega), h' 3 (by omega),
      h' 4 (by omega), h' 5 (by omega), h' 6 (by omega), h' 7 (by omega), h' 8 (by omega), h9]
    have : g 9 % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by decide)
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The final reduction: with `c = ⌊(h + 5) / 2¹³⁰⌋`, `(h + 5 c) mod 2¹³⁰` is `h mod p`,
for `h < 2 p`. -/
theorem reduce_eq {h : Nat} (hh : h < 2 ^ 131 - 10) :
    (h + 5 * ((h + 5) / 2 ^ 130)) % 2 ^ 130 = h % P := by
  rw [P_eq]
  rcases Nat.lt_or_ge (h + 5) (2 ^ 130) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_zero,
      Nat.add_zero]
  · have e : (h + 5) / 2 ^ 130 = 1 := by omega
    rw [e]
    omega

/-! ## The whole final reduction -/

theorem chainT_le (u : Nat → Nat) (hu : ∀ j < 10, u j ≤ 2 ^ 13) : ∀ k < 10, chainT u k ≤ 2 ^ 13 + 5
  | 0, _ => by have := hu 0 (by omega); simp only [chainT]; omega
  | k + 1, h => by
    have := chainT_le u hu k (by omega)
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
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> omega
    · have := hj j h hj'; omega
  have hvK : val (redK E) = val (fold E) := val_carryN _ 1 8 (by omega)
  have hK0 : redK E 0 = fold E 0 := carryN_below _ 1 8 0 (by omega)
  have hKm : ∀ j, 1 ≤ j → j < 9 → redK E j < 2 ^ 13 := fun j a b => carryN_lt _ 1 8 j a (by omega)
  have hK9 : redK E 9 ≤ 2 ^ 13 := by
    have : 2 ^ 117 * redK E 9 ≤ val (redK E) := by simp only [val]; omega
    omega
  have hK : ∀ j < 10, redK E j ≤ 2 ^ 13 := fun j hj' => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rcases Nat.lt_or_ge j 1 with h' | h'
      · rw [show j = 0 by omega, hK0]; omega
      · have := hKm j h' h; omega
    · rw [show j = 9 by omega]; exact hK9
  have hc : redC E ≤ 1 := by simp only [redC]; omega
  have hK' : ∀ j < 10, redK' E j < 2 ^ 32 - 2 ^ 19 := fun j hj' => by
    have := hK j hj'
    simp only [redK']; split <;> omega
  have hl : ∀ j < 9, carryN (redK' E) 0 9 j < 2 ^ 13 := fun j hj' => carryN_lt _ 0 9 j (by omega) (by omega)
  refine ⟨hH, hK, hK', ?_, fun j hj' => ?_⟩
  · have hm := val_mask_top (g := carryN (redK' E) 0 9) (g' := redL E) hl
      (fun k hk => by simp only [redL]; rw [iteF (by omega)]) (by simp [redL])
    rw [hm, val_carryN _ 0 9 (by omega)]
    have e : val (redK' E) = val (redK E) + 5 * redC E := by
      simp (config := {decide := true}) only [val, redK', iteT, ite_false]; omega
    rw [e, redC, reduce_eq (by omega), hvK, hv]
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
  split <;> simp [Nat.testBit_and]

/-- The clamped `r` of a key stored as four little-endian words. -/
theorem clamp_words {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    VG.Spec.Poly1305.clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by omega
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
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, subFlags, h], rfl, rfl, rfl, rfl⟩

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
  simp [Op2.eval, h]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp [Op2.eval, h]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp [Op2.eval, h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

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
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp [exec, ho]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

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
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp [exec, ho, State.load8, hin])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp [exec, ho, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

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
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k := Offset.sep p h (by omega) (by omega)

/-- Reading a word after writing one elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by omega)

theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ := Offset.disjoint p h (by omega) (by omega)

theorem sub_sub (p : Addr) {a len b len' : Nat} (h1 : b ≤ a) (h2 : a + len ≤ b + len')
    (_h3 : b + len' < 2 ^ 32) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p + BitVec.ofNat 64 b, len'⟩ := Offset.sub p h1 h2

/-! ## The state -/

/-- The state's region. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 128⟩

theorem ea {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {off : Nat} (h : off < 128) :
    State.addr (st + BitVec.ofNat 32 off) = State.addr st + BitVec.ofNat 64 off :=
  addr_add (by omega)

theorem inSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem outSt {st : BitVec 32} {s : State} (hw : stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions s.wr (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, hw, contains_off h (by omega)⟩

end VG.Proof.Poly1305.Arm
