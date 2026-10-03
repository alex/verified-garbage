import VerifiedGarbage.Proof.X448.Wide.Limbs
import Batteries.Logic

/-!
# X448: row multiplication and coefficient reduction

Untrusted: everything here is checked by Lean. Multiplication adds one row
at a time to a 16-word coefficient array. The upper coefficients fold
into eight limbs using the field prime's two non-leading terms.
-/

namespace VG.Proof.X448.Wide

open VG.Spec.X448 VG.Proof.X448

def addAt (f : Nat → Nat) (k v : Nat) (i : Nat) : Nat :=
  if i = k then f i + v else f i

theorem addAt_val (f : Nat → Nat) {n k : Nat} (hk : k < n) (v : Nat) :
    valN (addAt f k v) n = valN f n + radix ^ k * v :=
  valN_update hk (fun _ _ => rfl)

/-- The first `n` products of a row, at displacement `i`. -/
def addRow (f : Nat → Nat) (a : Nat) (g : Nat → Nat) (i : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => addAt (addRow f a g i n) (i + n) (a * g n)

theorem addRow_val (f g : Nat → Nat) (a : Nat) {i n : Nat} (h : i + n ≤ 16) :
    valN (addRow f a g i n) 16 = valN f 16 + radix ^ i * a * valN g n := by
  induction n with
  | zero => simp only [addRow, valN, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    rw [addRow, addAt_val _ (by omega), ih (by omega), valN_succ g n, Nat.pow_add]
    generalize radix ^ i = A
    generalize radix ^ n = B
    grind

theorem addRow_at (f g : Nat → Nat) (a i n k : Nat) :
    addRow f a g i n k = f k + if i ≤ k ∧ k < i + n then a * g (k - i) else 0 := by
  induction n with
  | zero => simp only [addRow, Nat.add_zero, show ¬ (i ≤ k ∧ k < i) by omega,
      ite_false, Nat.add_zero]
  | succ n ih =>
    simp only [addRow, addAt]
    by_cases hk : k = i + n
    · subst k
      rw [ite_eq_left rfl, ih, ite_eq_right (by omega), Nat.add_zero,
        ite_eq_left (by omega), Nat.add_sub_cancel_left]
    · rw [ite_eq_right hk, ih]
      have he : (i ≤ k ∧ k < i + n) ↔ (i ≤ k ∧ k < i + (n + 1)) := by omega
      simp only [he]

/-- The first `n` rows of the product of two eight-limb operands. -/
def rows (f g : Nat → Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | n + 1 => addRow (rows f g n) (f n) g n 8

theorem rows_val (f g : Nat → Nat) {n : Nat} (hn : n ≤ 8) :
    valN (rows f g n) 16 = valN f n * valN g 8 := by
  induction n with
  | zero => simp only [rows, valN, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ n ih =>
    rw [rows, addRow_val _ _ _ (by omega), ih (by omega), valN_succ f n, Nat.add_mul]

theorem rows_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < radix)
    (hg : ∀ i < 8, g i < radix) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    rows f g n k ≤ n * (radix - 1) ^ 2 := by
  induction n with
  | zero => simp only [rows, Nat.zero_mul, Nat.le_refl]
  | succ n ih =>
    rw [rows, addRow_at]
    have hp := ih (by omega)
    split
    · rename_i hk
      have h1 := hf n (by omega)
      have h2 := hg (k - n) (by omega)
      have hprod : f n * g (k - n) ≤ (radix - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

/-- Coefficients of degree 8–11 fold once; 12–15 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 8) + if k < 4 then f (k + 12) else f (k + 4) + f (k + 8)

theorem reduced_val (f : Nat → Nat) :
    valN (reduced f) 8 =
      (valN f 4 + valN (fun i => f (8 + i)) 4 + valN (fun i => f (12 + i)) 4) +
      half * (valN (fun i => f (4 + i)) 4 + valN (fun i => f (12 + i)) 4 +
        valN (fun i => f (8 + i)) 4 + valN (fun i => f (12 + i)) 4) := by
  rw [show 8 = 4 + 4 from rfl, valN_split]
  apply congrArg₂ (· + ·)
  · rw [← valN_add, ← valN_add]
    apply valN_congr
    intro i hi
    simp only [reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (radix ^ 4 * ·)
    rw [← valN_add, ← valN_add, ← valN_add]
    apply valN_congr
    intro i _
    simp only [reduced, ite_eq_right (by omega : ¬ 4 + i < 4)]
    rw [show 4 + i + 8 = 12 + i by omega, show 4 + i + 4 = 8 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : valN (reduced f) 8 % P = valN f 16 % P := by
  have hp : P = full - half - 1 := by decide +kernel
  have he : valN f 16 = valN (reduced f) 8 +
      P * (valN (fun i => f (8 + i)) 4 + (half + 1) * valN (fun i => f (12 + i)) 4) := by
    rw [reduced_val, show 16 = 8 + 8 from rfl, valN_split,
      show 8 = 4 + 4 from rfl, valN_split, valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 116) :
    ∀ i < 8, reduced f i < 2 ^ 118 := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 8) (by omega)
  simp only [reduced]
  split
  · have h2 := h (i + 12) (by omega); omega
  · have h2 := h (i + 4) (by omega); omega

/-- A product coefficient accumulated along its diagonal. -/
def colSum (f g : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => colSum f g k n + if n ≤ k ∧ k < n + 8 then f n * g (k - n) else 0

theorem colSum_eq (f g : Nat → Nat) (k n : Nat) :
    colSum f g k n = rows f g n k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [colSum, rows, addRow_at, ih]

theorem rows_congr {f g f' g' : Nat → Nat} (hf : ∀ i < 8, f i = f' i)
    (hg : ∀ i < 8, g i = g' i) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    rows f g n k = rows f' g' n k := by
  rw [← colSum_eq, ← colSum_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [colSum, colSum, ih (by omega)]
    split
    · rename_i h
      rw [hf n (by omega), hg (k - n) (by omega)]
    · rfl

end VG.Proof.X448.Wide
