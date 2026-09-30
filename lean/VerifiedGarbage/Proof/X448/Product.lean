import VerifiedGarbage.Proof.X448.Limbs

/-!
# X448: row multiplication and coefficient reduction

Untrusted: everything here is checked by Lean. Multiplication adds one row
at a time to a 32-word coefficient array. The upper coefficients fold
into sixteen limbs using the field prime's two non-leading terms.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def addAt (f : Nat → Nat) (k v : Nat) (i : Nat) : Nat :=
  if i = k then f i + v else f i

theorem addAt_val (f : Nat → Nat) {n k : Nat} (hk : k < n) (v : Nat) :
    valN (addAt f k v) n = valN f n + radix ^ k * v :=
  valN_update hk (fun _ _ => rfl)

/-- The first `n` products of a row, at displacement `i`. -/
def addRow (f : Nat → Nat) (a : Nat) (g : Nat → Nat) (i : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => addAt (addRow f a g i n) (i + n) (a * g n)

theorem addRow_val (f g : Nat → Nat) (a : Nat) {i n : Nat} (h : i + n ≤ 32) :
    valN (addRow f a g i n) 32 = valN f 32 + radix ^ i * a * valN g n := by
  induction n with
  | zero => simp only [addRow, valN, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    rw [addRow, addAt_val _ (by omega), ih (by omega), valN_succ g n, Nat.pow_add]
    ring

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

/-- The first `n` rows of the product of two sixteen-limb operands. -/
def rows (f g : Nat → Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | n + 1 => addRow (rows f g n) (f n) g n 16

theorem rows_val (f g : Nat → Nat) {n : Nat} (hn : n ≤ 16) :
    valN (rows f g n) 32 = valN f n * valN g 16 := by
  induction n with
  | zero => simp only [rows, valN, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ n ih =>
    rw [rows, addRow_val _ _ _ (by omega), ih (by omega), valN_succ f n]
    ring

theorem rows_bound {f g : Nat → Nat} (hf : ∀ i < 16, f i < radix)
    (hg : ∀ i < 16, g i < radix) {n : Nat} (hn : n ≤ 16) (k : Nat) :
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

/-- Coefficients of degree 16–23 fold once; 24–31 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 16) + if k < 8 then f (k + 24) else f (k + 8) + f (k + 16)

theorem reduced_val (f : Nat → Nat) :
    valN (reduced f) 16 =
      (valN f 8 + valN (fun i => f (16 + i)) 8 + valN (fun i => f (24 + i)) 8) +
      half * (valN (fun i => f (8 + i)) 8 + valN (fun i => f (24 + i)) 8 +
        valN (fun i => f (16 + i)) 8 + valN (fun i => f (24 + i)) 8) := by
  rw [show 16 = 8 + 8 from rfl, valN_split]
  apply congrArg₂ (· + ·)
  · rw [← valN_add, ← valN_add]
    apply valN_congr
    intro i hi
    simp only [reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (radix ^ 8 * ·)
    rw [← valN_add, ← valN_add, ← valN_add]
    apply valN_congr
    intro i _
    simp only [reduced, ite_eq_right (by omega : ¬ 8 + i < 8)]
    rw [show 8 + i + 16 = 24 + i by omega, show 8 + i + 8 = 16 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : valN (reduced f) 16 % P = valN f 32 % P := by
  have hp : P = full - half - 1 := by decide +kernel
  have he : valN f 32 = valN (reduced f) 16 +
      P * (valN (fun i => f (16 + i)) 8 + (half + 1) * valN (fun i => f (24 + i)) 8) := by
    rw [reduced_val, show 32 = 16 + 16 from rfl, valN_split,
      show 16 = 8 + 8 from rfl, valN_split, valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 32, f i < 2 ^ 60) :
    ∀ i < 16, reduced f i < 2 ^ 62 := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 16) (by omega)
  simp only [reduced]
  split
  · have h2 := h (i + 24) (by omega); omega
  · have h2 := h (i + 8) (by omega); omega

end VG.Proof.X448
