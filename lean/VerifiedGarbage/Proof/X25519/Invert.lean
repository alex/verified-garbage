import VerifiedGarbage.Spec.X25519
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# X25519: the inversion `z^(p-2)` as an addition chain

The spec's `pow` is the power of the monoid `GF(p)` (with Mathlib's ring
structure on `Fin p`), and `invert`, the addition chain of ref10's `fe_invert`
(254 squarings and 11 multiplications, in the order implementations compute
them), is `z^(p-2)`. An implementation of the chain is proven against
`invert`, one multiplication or run of squarings (`sqn`) at a time.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519
open Fin.CommRing

theorem pow_eq (a : Fe) (e : Nat) : pow a e = a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [pow]
    by_cases h0 : e = 0
    · simp [h0]
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega)]
      conv => rhs; rw [← Nat.div_add_mod e 2]
      rcases Nat.mod_two_eq_zero_or_one e with h | h <;>
        simp only [h, ite_true, Nat.one_ne_zero, ite_false] <;> ring

/-- `x` squared `n` times: `x^(2^n)`. -/
def sqn (x : Fe) : Nat → Fe
  | 0 => x
  | n + 1 => sqn x n * sqn x n

theorem sqn_eq (x : Fe) (n : Nat) : sqn x n = x ^ (2 ^ n) := by
  induction n with
  | zero => simp [sqn]
  | succ n ih => rw [sqn, ih, Nat.pow_succ, pow_mul]; ring

theorem sqn_succ' (x : Fe) (n : Nat) : sqn x (n + 1) = sqn (x * x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sqn, ih, sqn]

/-- ref10's `fe_invert(z)`: the exponents of `z` in the comments. -/
def invert (z : Fe) : Fe :=
  let t0 := z * z                 -- 2
  let t1 := sqn t0 2              -- 8
  let t1 := z * t1                -- 9
  let t0 := t0 * t1               -- 11
  let t2 := t0 * t0               -- 22
  let t1 := t1 * t2               -- 31 = 2^5 - 1
  let t2 := sqn t1 5
  let t1 := t2 * t1               -- 2^10 - 1
  let t2 := sqn t1 10
  let t2 := t2 * t1               -- 2^20 - 1
  let t3 := sqn t2 20
  let t2 := t3 * t2               -- 2^40 - 1
  let t2 := sqn t2 10
  let t1 := t2 * t1               -- 2^50 - 1
  let t2 := sqn t1 50
  let t2 := t2 * t1               -- 2^100 - 1
  let t3 := sqn t2 100
  let t2 := t3 * t2               -- 2^200 - 1
  let t2 := sqn t2 50
  let t1 := t2 * t1               -- 2^250 - 1
  let t1 := sqn t1 5
  t1 * t0                         -- 2^255 - 21 = p - 2

theorem invert_eq (z : Fe) : invert z = pow z (P - 2) := by
  rw [pow_eq, invert]
  simp only [sqn_eq, ← pow_mul, ← pow_add, ← pow_succ, ← pow_succ', ← pow_two, mul_comm z,
    ← pow_mul]
  congr 1

end VG.Proof.X25519
