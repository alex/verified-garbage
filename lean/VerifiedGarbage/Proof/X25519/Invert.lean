import VerifiedGarbage.Spec.X25519

/-!
# X25519: the inversion `z^(p-2)` as an addition chain

`invert`, the addition chain of ref10's `fe_invert` (254 squarings and 11
multiplications, in the order implementations compute them), is the spec's
`pow z (p-2)`, shown on the residues (`pw z e`, the residue of `z^e`), without
Mathlib's ring structure on `Fin p`. An implementation of the chain is proven
against `invert`, one multiplication or run of squarings (`sqn`) at a time.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- `x` squared `n` times: `x^(2^n)`. -/
def sqn (x : Fe) : Nat → Fe
  | 0 => x
  | n + 1 => sqn x n * sqn x n

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

/-- `z^e`, computed on the residue. -/
def pw (z : Fe) (e : Nat) : Fe := Fin.ofNat P (z.val ^ e)

theorem pw_one (z : Fe) : pw z 1 = z :=
  Fin.ext (by simp only [pw, Fin.val_ofNat, Nat.pow_one, Nat.mod_eq_of_lt z.isLt])

theorem pw_zero (z : Fe) : pw z 0 = 1 := by
  show Fin.ofNat P (z.val ^ 0) = 1
  rw [Nat.pow_zero]
  rfl

theorem pw_mul (z : Fe) (a b : Nat) : pw z a * pw z b = pw z (a + b) :=
  Fin.ext (by simp only [pw, Fin.val_mul, Fin.val_ofNat, Nat.pow_add, ← Nat.mul_mod])

theorem pw_sq (z : Fe) (a : Nat) : pw (z * z) a = pw z (2 * a) :=
  Fin.ext (by simp only [pw, Fin.val_mul, Fin.val_ofNat, ← Nat.pow_mod, Nat.pow_mul, Nat.pow_two])

theorem sqn_pw (z : Fe) (a n : Nat) : sqn (pw z a) n = pw z (a * 2 ^ n) := by
  induction n with
  | zero => rw [sqn, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [sqn, ih, pw_mul, Nat.pow_succ, Nat.mul_two, Nat.mul_add]

theorem pow_pw (a : Fe) (e : Nat) : pow a e = pw a e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [pow]
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, h0]
      exact Fin.ext (by simp only [pw, Fin.val_ofNat, Nat.pow_zero]; rfl)
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega), pw_sq]
      by_cases h : e % 2 = 0
      · rw [ite_eq_left h]; exact congrArg (pw a) (by omega)
      · rw [ite_eq_right h, ← congrArg (· * _) (pw_one a), pw_mul]
        exact congrArg (pw a) (by omega)

theorem invert_eq (z : Fe) : invert z = pow z (P - 2) := by
  rw [pow_pw, ← congrArg invert (pw_one z)]
  simp only [invert, pw_mul, sqn_pw]
  exact congrArg (pw z) (by decide)

end VG.Proof.X25519
