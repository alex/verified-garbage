import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Spec.Poly1305

/-!
# Poly1305 on 32-bit ARM: the arithmetic in radix `2¹³`

Untrusted: everything here is checked by Lean. The numbers the code computes
(see `Impl/Poly1305/Arm.lean`), as natural numbers: a number is ten limbs
`f 0, …, f 9` of 13 bits (`val`), possibly larger; the columns of a product
modulo `p` (`col`); the carries (`carryN`); the limbs of four 32-bit words
(`mlimb`) and back (`toWords`); and the final reduction.
-/

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
  | 0 => le_rfl
  | n + 1 => Nat.add_le_add (rsum_le h n) (h n)

theorem rsum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : rsum f m ≤ rsum f n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · rw [show m = n + 1 by omega]

theorem rsum_const (c : Nat) : ∀ n, rsum (fun _ => c) n = n * c
  | 0 => by simp [rsum]
  | n + 1 => by rw [rsum, rsum_const c n]; ring

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
        show (i + j) % 10 - j = i by omega]; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j ≤ (i + j) % 10 by omega)),
        show (i + j) % 10 + 10 - j = i by omega]; ring
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
  | 0, _ => le_rfl
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

/-- The columns of `h r`, as a number, are `h r` modulo `p`. -/
theorem val_col (h r : Nat → Nat) : val (col h r) % P = val h * val r % P := by
  have key : val h * val r = val (col h r) + P *
      (h 1 * r 9 + h 2 * r 8 + h 3 * r 7 + h 4 * r 6 + h 5 * r 5 + h 6 * r 4 + h 7 * r 3 + h 8 * r 2 +
        h 9 * r 1 +
      2 ^ 13 * (h 2 * r 9 + h 3 * r 8 + h 4 * r 7 + h 5 * r 6 + h 6 * r 5 + h 7 * r 4 + h 8 * r 3 +
        h 9 * r 2) +
      2 ^ 26 * (h 3 * r 9 + h 4 * r 8 + h 5 * r 7 + h 6 * r 6 + h 7 * r 5 + h 8 * r 4 + h 9 * r 3) +
      2 ^ 39 * (h 4 * r 9 + h 5 * r 8 + h 6 * r 7 + h 7 * r 6 + h 8 * r 5 + h 9 * r 4) +
      2 ^ 52 * (h 5 * r 9 + h 6 * r 8 + h 7 * r 7 + h 8 * r 6 + h 9 * r 5) +
      2 ^ 65 * (h 6 * r 9 + h 7 * r 8 + h 8 * r 7 + h 9 * r 6) +
      2 ^ 78 * (h 7 * r 9 + h 8 * r 8 + h 9 * r 7) +
      2 ^ 91 * (h 8 * r 9 + h 9 * r 8) +
      2 ^ 104 * (h 9 * r 9)) := by
    simp only [val, col, rsum, coef, P_eq]
    norm_num
    ring
  rw [key, Nat.add_mul_mod_self_left]

/-! ## Carrying -/

/-- Column `k`'s bits from 13 up moved to column `k + 1`. -/
def cstep (f : Nat → Nat) (k : Nat) : Nat → Nat :=
  fun j => if j = k then f k % 2 ^ 13 else if j = k + 1 then f (k + 1) + f k / 2 ^ 13 else f j

theorem val_cstep (f : Nat → Nat) {k : Nat} (hk : k < 9) : val (cstep f k) = val f := by
  interval_cases k <;> simp [val, cstep] <;> omega

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
    · simp only [e, ite_true]; exact Nat.mod_lt _ (by norm_num)
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
  · rw [f0]; exact Nat.mod_lt _ (by norm_num)
  · rw [f1]; omega
  · intro j h2 h10
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [fj j h2 h]; exact hl j h
    · rw [show j = 9 by omega, f9]; exact Nat.mod_lt _ (by norm_num)

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
  ring

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
      simp only [spre, rsum]; ring
    rw [e, show 13 * (k + 1) = 13 * k + 13 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (u k)]

theorem chainT_top (u : Nat → Nat) : chainT u 9 / 2 ^ 13 = (val u + 5) / 2 ^ 130 := by
  rw [chainT_eq, Nat.add_comm (u 9)]
  have e : val u + 5 = (spre u 9 + 5) + 2 ^ 117 * u 9 := by
    simp only [val, spre, rsum]; ring
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
    have : g 9 % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by norm_num)
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
    · interval_cases j <;> omega
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
      simp only [val, redK', iteT]; norm_num; ring
    rw [e, redC, reduce_eq (by omega), hvK, hv]
  · simp only [redL]
    split
    · exact Nat.mod_lt _ (by norm_num)
    · exact hl j (by omega)

/-! ## Clamping -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_left ha
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
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by ring
  rw [VG.Spec.Poly1305.clamp, e, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) by norm_num,
    land_split32 h0 (by norm_num), land_split32 h1 (by norm_num), land_split32 h2 (by norm_num)]

theorem and_lt {k m : Nat} (h : m < 2 ^ 28) : (k &&& m) < 2 ^ 28 :=
  lt_of_le_of_lt Nat.and_le_right h

theorem and_fffffffc_mod (k : Nat) : (k &&& 0x0ffffffc) % 2 = 0 := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc &&& 2 ^ 1 - 1 : Nat) = 0 by decide, Nat.and_zero]

end VG.Proof.Poly1305.Arm
