import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Carry

/-!
# Bounds of a product's coefficients and carries

Untrusted: everything here is checked by Lean. Operand limbs below `Ib`
(sums and differences of reduced elements) give coefficients below `2¹²⁰`,
carries of one word, and limbs of the result below `Mb`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG.Proof.X448.Wide (rows reduced addRow_at radix)

/-- The bound of a reduced element's limbs. -/
def Mb : Nat := 2 ^ 56 + 2 ^ 8

/-- The bound of a multiplication's operand limbs. -/
def Ib : Nat := 3 * 2 ^ 56 + 2 ^ 9

/-- The number of products in a schoolbook coefficient. -/
def cnt (k : Nat) : Nat := ((List.range 8).filter fun n => n ≤ k ∧ k < n + 8).length

theorem rows_le {f g : Nat → Nat} {B : Nat} (hf : ∀ i < 8, f i ≤ B) (hg : ∀ i < 8, g i ≤ B)
    (k : Nat) : rows f g 8 k ≤ cnt k * (B * B) := by
  have : ∀ n ≤ 8, rows f g n k ≤ ((List.range n).filter fun m => m ≤ k ∧ k < m + 8).length * (B * B) := by
    intro n hn
    induction n with
    | zero => simp [rows]
    | succ n ih =>
      rw [rows, addRow_at, List.range_succ, List.filter_append, List.length_append]
      have := ih (by omega)
      split
      · rename_i h
        have hp : f n * g (k - n) ≤ B * B :=
          Nat.mul_le_mul (hf n (by omega)) (hg (k - n) (by omega))
        simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true,
          List.length_singleton, Nat.add_mul, Nat.one_mul]
        omega
      · rename_i h
        simp only [List.filter_cons, List.filter_nil, decide_eq_false h, Bool.false_eq_true,
          ite_false, List.length_nil, Nat.add_zero]
        omega
  exact this 8 (Nat.le_refl _)

/-- The number of products in coefficient `k` of a reduced product. -/
def rc (k : Nat) : Nat := cnt k + cnt (k + 8) + if k < 4 then cnt (k + 12) else cnt (k + 4) + cnt (k + 8)

theorem rc_eq : rc 0 = 11 ∧ rc 1 = 10 ∧ rc 2 = 9 ∧ rc 3 = 8 ∧ rc 4 = 18 ∧ rc 5 = 16 ∧ rc 6 = 14 ∧
    rc 7 = 12 := by decide

theorem reduced_le {f g : Nat → Nat} {B : Nat} (hf : ∀ i < 8, f i ≤ B) (hg : ∀ i < 8, g i ≤ B)
    (k : Nat) : reduced (rows f g 8) k ≤ rc k * (B * B) := by
  have r := rows_le hf hg
  simp only [reduced, rc]
  split
  · have := r k; have := r (k + 8); have := r (k + 12)
    rw [Nat.add_mul, Nat.add_mul]; omega
  · have := r k; have := r (k + 8); have := r (k + 4)
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega

/-- What the code needs of a product's coefficients. -/
structure Fits (r : Nat → Nat) : Prop where
  low : ∀ n < 4, r n + chain r 0 n < 2 ^ 120
  high : ∀ n < 4, r (4 + n) + chain r 4 n < 2 ^ 120
  c₀ : chainLimb r 0 0 + chain r 4 4 < 2 ^ 64
  c₄ : chainLimb r 4 0 + chain r 0 4 + chain r 4 4 < 2 ^ 64
  out : ∀ i < 8, out r i < Mb

theorem fits {r : Nat → Nat} (h : ∀ k < 8, r k ≤ rc k * ((Ib - 1) * (Ib - 1))) : Fits r := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := rc_eq
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  rw [e4] at h4; rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  simp only [Ib, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at h0 h1 h2 h3 h4 h5 h6 h7
  have l1 : chain r 0 1 = r 0 / radix := by simp [chain]
  have l2 : chain r 0 2 = (r 1 + chain r 0 1) / radix := by simp [chain]
  have l3 : chain r 0 3 = (r 2 + chain r 0 2) / radix := by simp [chain]
  have l4 : chain r 0 4 = (r 3 + chain r 0 3) / radix := by simp [chain]
  have m1 : chain r 4 1 = r 4 / radix := by simp [chain]
  have m2 : chain r 4 2 = (r 5 + chain r 4 1) / radix := by simp [chain]
  have m3 : chain r 4 3 = (r 6 + chain r 4 2) / radix := by simp [chain]
  have m4 : chain r 4 4 = (r 7 + chain r 4 3) / radix := by simp [chain]
  have z0 : chain r 0 0 = 0 := rfl
  have y0 : chain r 4 0 = 0 := rfl
  simp only [radix, Nat.reducePow] at l1 l2 l3 l4 m1 m2 m3 m4
  have k00 : chainLimb r 0 0 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k01 : chainLimb r 0 1 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k02 : chainLimb r 0 2 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k03 : chainLimb r 0 3 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k40 : chainLimb r 4 0 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k41 : chainLimb r 4 1 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k42 : chainLimb r 4 2 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k43 : chainLimb r 4 3 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  refine ⟨fun n hn => ?_, fun n hn => ?_, by omega, by omega, fun i hi => ?_⟩
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    all_goals omega
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    all_goals simp only [Nat.reduceAdd]; omega
  · simp only [Mb]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp only [out, radix, Nat.reducePow]; omega

end VG.Proof.Curve448.AArch64.Fast
