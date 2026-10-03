import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp

/-!
# Karatsuba's columns are the reduced product's coefficients

Untrusted: everything here is checked by Lean. For each column `d < 4` of a
multiplication (or a square), the signed sums of products that `sem`
accumulates in `L` and `H` are the coefficients `d` and `d + 4` of the
schoolbook product folded with `2⁴⁴⁸ = 2²²⁴ + 1`, `reduced (rows f g 8)`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Proof.X448.Wide (rows reduced addRow addRow_at addAt)

theorem pairs_0 : pairs 0 = [(0, 0)] := by decide
theorem pairs_1 : pairs 1 = [(0, 1), (1, 0)] := by decide
theorem pairs_2 : pairs 2 = [(0, 2), (1, 1), (2, 0)] := by decide
theorem pairs_3 : pairs 3 = [(0, 3), (1, 2), (2, 1), (3, 0)] := by decide
theorem pairs_4 : pairs 4 = [(1, 3), (2, 2), (3, 1)] := by decide
theorem pairs_5 : pairs 5 = [(2, 3), (3, 2)] := by decide
theorem pairs_6 : pairs 6 = [(3, 3)] := by decide
theorem pairs_7 : pairs 7 = [] := by decide

theorem sqPairs_0 : sqPairs 0 = [(0, 0)] := by decide
theorem sqPairs_1 : sqPairs 1 = [(0, 1)] := by decide
theorem sqPairs_2 : sqPairs 2 = [(0, 2), (1, 1)] := by decide
theorem sqPairs_3 : sqPairs 3 = [(0, 3), (1, 2)] := by decide
theorem sqPairs_4 : sqPairs 4 = [(1, 3), (2, 2)] := by decide
theorem sqPairs_5 : sqPairs 5 = [(2, 3)] := by decide
theorem sqPairs_6 : sqPairs 6 = [(3, 3)] := by decide
theorem sqPairs_7 : sqPairs 7 = [] := by decide

/-- The schoolbook coefficients, one sum per diagonal. -/
theorem rows_eq (f g : Nat → Nat) (k : Nat) :
    rows f g 8 k = (if k < 8 then f 0 * g k else 0) +
      (if 1 ≤ k ∧ k < 9 then f 1 * g (k - 1) else 0) +
      (if 2 ≤ k ∧ k < 10 then f 2 * g (k - 2) else 0) +
      (if 3 ≤ k ∧ k < 11 then f 3 * g (k - 3) else 0) +
      (if 4 ≤ k ∧ k < 12 then f 4 * g (k - 4) else 0) +
      (if 5 ≤ k ∧ k < 13 then f 5 * g (k - 5) else 0) +
      (if 6 ≤ k ∧ k < 14 then f 6 * g (k - 6) else 0) +
      (if 7 ≤ k ∧ k < 15 then f 7 * g (k - 7) else 0) := by
  simp only [rows, addRow_at]
  simp only [Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero]

section Mul
open Mul

variable (f g : Nat → Nat) (v : Src → Nat)
  (h0 : ∀ i j, i < 4 → j < 4 → (v (src 0 (i, j)).1 : Int) * v (src 0 (i, j)).2 = f i * g j)
  (h1 : ∀ i j, i < 4 → j < 4 → (v (src 1 (i, j)).1 : Int) * v (src 1 (i, j)).2 = f (i + 4) * g (j + 4))
  (h2 : ∀ i j, i < 4 → j < 4 → (v (src 2 (i, j)).1 : Int) * v (src 2 (i, j)).2 =
    (f i + f (i + 4)) * (g j + g (j + 4)))
include h0 h1 h2

theorem mulCol_ok (e : Env) {d : Nat} (hd : d < 4) :
    sem v e (column d) L = reduced (rows f g 8) d ∧
    sem v e (column d) H = reduced (rows f g 8) (d + 4) := by
  obtain rfl | rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  all_goals
    simp (config := {decide := true}) only [column, terms, Nat.reduceAdd, pairs_0, pairs_1,
      pairs_2, pairs_3, pairs_4, pairs_5, pairs_6, pairs_7, start, addTo, shared,
      List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, sem, opSem, List.foldl, target, upd, ite_true, ite_false,
      h0, h1, h2]
    simp only [reduced, rows_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
      and_true, and_false, and_self, ite_true, ite_false, Nat.add_zero,
      Nat.zero_add]
    constructor <;> (push_cast; simp only [Int.add_mul, Int.mul_add, Int.mul_comm]; omega)

end Mul

section Sqr
open Sqr

variable (f : Nat → Nat) (v : Src → Nat)
  (h0 : ∀ i j, i ≤ j → j < 4 → (v (src 0 (i, j)).1 : Int) * v (src 0 (i, j)).2 =
    (if i = j then 1 else 2) * f i * f j)
  (h1 : ∀ i j, i ≤ j → j < 4 → (v (src 1 (i, j)).1 : Int) * v (src 1 (i, j)).2 =
    (if i = j then 1 else 2) * f (i + 4) * f (j + 4))
  (h2 : ∀ i j, i ≤ j → j < 4 → (v (src 2 (i, j)).1 : Int) * v (src 2 (i, j)).2 =
    (if i = j then 1 else 2) * (f i + f (i + 4)) * (f j + f (j + 4)))
include h0 h1 h2

theorem sqrCol_ok (e : Env) {d : Nat} (hd : d < 4) :
    sem v e (column d) L = reduced (rows f f 8) d ∧
    sem v e (column d) H = reduced (rows f f 8) (d + 4) := by
  obtain rfl | rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  all_goals
    simp (config := {decide := true}) only [column, terms, Nat.reduceAdd, sqPairs_0, sqPairs_1,
      sqPairs_2, sqPairs_3, sqPairs_4, sqPairs_5, sqPairs_6, sqPairs_7, start, addTo,
      List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, sem, opSem, List.foldl, target, upd, ite_true, ite_false,
      h0, h1, h2]
    simp only [reduced, rows_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
      and_true, and_false, and_self, ite_true, ite_false, Nat.add_zero,
      Nat.zero_add]
    constructor <;> (push_cast; simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm,
      Int.mul_left_comm, Int.one_mul]; omega)

end Sqr

end VG.Proof.Curve448.AArch64.Fast
