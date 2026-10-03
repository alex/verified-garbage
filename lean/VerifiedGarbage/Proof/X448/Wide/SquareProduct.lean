import VerifiedGarbage.Proof.X448.Wide.Product

/-! Untrusted: symmetric diagonal accumulation for an eight-limb square. -/
namespace VG.Proof.X448.Wide

def sqrSum (f : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sqrSum f k n + if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then f n * f (k - n) else 2 * (f n * f (k - n)) else 0

theorem sqrSum_eq (f : Nat → Nat) {k : Nat} (hk : k < 16) :
    sqrSum f k 8 = rows f f 8 k := by
  rw [← colSum_eq]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  all_goals (simp [sqrSum, colSum] <;> grind)

theorem sqrSum_le {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) (k : Nat) :
    sqrSum f k n ≤ sqrSum f k m := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega
    exact Nat.le_refl _
  | succ m ih =>
    by_cases h : n = m + 1
    · subst n; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (by rw [sqrSum]; omega)

theorem sqrSum_bound {f : Nat → Nat} (hf : ∀ i < 8, f i < radix)
    {n k : Nat} (hn : n ≤ 8) (hk : k < 16) : sqrSum f k n < 2 ^ 116 := by
  have h := sqrSum_le hn f k
  rw [sqrSum_eq f hk] at h
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (rows_bound hf hf (by decide) k)) (by decide)

end VG.Proof.X448.Wide
