import VerifiedGarbage.Spec.X448

/-!
# X448: the inversion `z^(p-2)` as an addition chain

An addition chain for `z^(2⁴⁴⁸ - 2²²⁴ - 3)`, with runs of squarings shared by
the targets. The chain first builds `z^(2²²² - 1)`, then its two final
factors.
-/

namespace VG.Proof.X448

open VG.Spec.X448

/-- `x` squared `n` times: `x^(2^n)`. -/
def sqn (x : Fe) : Nat → Fe
  | 0 => x
  | n + 1 => sqn x n * sqn x n

theorem sqn_succ' (x : Fe) (n : Nat) : sqn x (n + 1) = sqn (x * x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sqn, ih, sqn]

/-- An addition chain for `z^(P - 2)`. The comments give the exponent
of each intermediate result. -/
def invert (z : Fe) : Fe :=
  let t2 := sqn z 1 * z            -- 2^2 - 1
  let t4 := sqn t2 2 * t2          -- 2^4 - 1
  let t8 := sqn t4 4 * t4          -- 2^8 - 1
  let t16 := sqn t8 8 * t8         -- 2^16 - 1
  let t32 := sqn t16 16 * t16      -- 2^32 - 1
  let t64 := sqn t32 32 * t32      -- 2^64 - 1
  let t128 := sqn t64 64 * t64     -- 2^128 - 1
  let t192 := sqn t128 64 * t64    -- 2^192 - 1
  let t208 := sqn t192 16 * t16    -- 2^208 - 1
  let t216 := sqn t208 8 * t8      -- 2^216 - 1
  let t220 := sqn t216 4 * t4      -- 2^220 - 1
  let t222 := sqn t220 2 * t2      -- 2^222 - 1
  let t223 := sqn t222 1 * z       -- 2^223 - 1
  sqn t223 225 * (sqn t222 2 * z)

/-- `z^e`, computed on the residue. -/
def pw (z : Fe) (e : Nat) : Fe := Fin.ofNat P (z.val ^ e)

theorem pw_one (z : Fe) : pw z 1 = z :=
  Fin.ext (by simp only [pw, Fin.val_ofNat, Nat.pow_one, Nat.mod_eq_of_lt z.isLt])

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
      show (1 : Fe) = Fin.ofNat P (a.val ^ 0)
      rw [Nat.pow_zero]
      rfl
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega), pw_sq]
      by_cases h : e % 2 = 0
      · rw [ite_eq_left h]; exact congrArg (pw a) (by omega)
      · rw [ite_eq_right h, ← congrArg (· * _) (pw_one a), pw_mul]
        exact congrArg (pw a) (by omega)

theorem invert_eq (z : Fe) : invert z = pow z (P - 2) := by
  rw [pow_pw, ← congrArg invert (pw_one z)]
  simp only [invert, pw_mul, sqn_pw]
  exact congrArg (pw z) (by decide +kernel)

end VG.Proof.X448
