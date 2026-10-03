import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Math
import VerifiedGarbage.Impl.Curve448.AArch64.Neon

/-!
# Which limbs each product multiplies

Untrusted: everything here is checked by Lean. Product `p` of a half multiplies
half-limb `ia p` of the first operand by half-limb `ib p` of the second, at
coefficient `ia p + ib p`; the products at coefficient `q` are, up to order,
the terms of `cv x y q` (`perm_q`, by evaluation).
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Impl.Curve448.AArch64.Neon

def ia (p : Prod) : Nat := 2 * p.i + (if p.hi then 1 else 0)
def ib (p : Prod) : Nat :=
  if p.bv < 4 then 2 * p.bv + (if p.hi then 1 else 0) else 2 * (p.bv - 4) + (if p.hi then 1 else 0) - 1

/-- The terms `(i, q - i)` of coefficient `q`. -/
def pairsQ (q : Nat) : List (Nat × Nat) :=
  ((List.range 8).filter fun i => i ≤ q ∧ q - i < 8).map fun i => (i, q - i)

theorem prods_pos : ∀ p ∈ prods, p.pos = ia p + ib p ∧ ia p < 8 ∧ ib p < 8 ∧
    (p.bv ≥ 4 → (p.hi = false → p.bv ≠ 4) ∧ (p.hi = true → p.bv ≠ 8)) := by decide

theorem perm_q : ∀ q < 15, List.Perm ((prods.filter fun p => p.pos == q).map fun p => (ia p, ib p)) (pairsQ q) := by
  decide

theorem cv_pairs (x y : Nat → Nat) : ∀ q < 15, cv x y q = ((pairsQ q).map fun ij => x ij.1 * y ij.2).sum := by
  intro q hq
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q
  all_goals first | omega | (simp [cv, pairsQ, List.range, List.range.loop]; try ring_nf)

end VG.Proof.Curve448.AArch64.Neon
