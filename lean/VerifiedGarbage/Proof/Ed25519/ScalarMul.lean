import VerifiedGarbage.Spec.Ed25519

/-!
# Scalar multiplication, from high bits to low bits

The loop accumulates the very same extended-coordinate values as `pointMul`,
rather than relying on an unproved group-law identity. At bit n its
accumulator is `[floor(s/2^(n+1))] [2^(n+1)]P`. Adding `[2^n]P` exactly when
bit n is one gives the next invariant. Powers can be computed in small batches
so the scratch space remains bounded.
-/

namespace VG.Proof.Ed25519

open VG.Spec.Ed25519

/-- Exactly n doublings, preserving the specification's coordinates. -/
def powerPoint (p : Point) : Nat → Point
  | 0 => p
  | n + 1 => pointAdd (powerPoint p n) (powerPoint p n)

theorem powerPoint_add (p : Point) (n k : Nat) :
    powerPoint p (n + k) = powerPoint (powerPoint p n) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, powerPoint, ih, powerPoint]

theorem pointMul_zero (p : Point) : pointMul 0 p = identity := by
  rw [pointMul, ite_eq_left rfl]

theorem pointMul_step (s : Nat) (p : Point) :
    pointMul s p =
      if s % 2 = 0 then pointMul (s / 2) (pointAdd p p)
      else pointAdd (pointMul (s / 2) (pointAdd p p)) p := by
  by_cases hs : s = 0
  · subst hs
    simp only [Nat.zero_mod, Nat.zero_div, ite_true, pointMul_zero]
  · conv => lhs; rw [pointMul, ite_eq_right hs]

def after (s : Nat) (p : Point) (n : Nat) : Point :=
  pointMul (s / 2 ^ n) (powerPoint p n)

theorem after_step (s : Nat) (p : Point) (n : Nat) :
    after s p n = if (s / 2 ^ n) % 2 = 0 then after s p (n + 1)
      else pointAdd (after s p (n + 1)) (powerPoint p n) := by
  simp only [after, powerPoint, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact pointMul_step _ _

theorem after_zero (s : Nat) (p : Point) : after s p 0 = pointMul s p := by
  simp only [after, Nat.pow_zero, Nat.div_one, powerPoint]

theorem after_top (s n : Nat) (p : Point) (hs : s < 2 ^ n) : after s p n = identity := by
  rw [after, Nat.div_eq_of_lt hs, pointMul_zero]

end VG.Proof.Ed25519
