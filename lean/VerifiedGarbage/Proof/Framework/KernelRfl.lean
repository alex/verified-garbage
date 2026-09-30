import Lean.Meta.Closure
import Lean.Elab.Tactic.Basic

/-!
# `rfl`, checked by the kernel alone

Untrusted: this only changes how proofs are found; the kernel checks them.

`rfl` has the elaborator check that the two sides are definitionally equal
before the kernel checks it again, and the elaborator's `whnf` is much slower
than the kernel's on terms that take a long evaluation (e.g. the constant-time
analysis of code whose immediates are variables, which it never looks at).
`kernel_rfl` proves `lhs = rhs` by `Eq.refl lhs` in an auxiliary theorem that
only the kernel checks, as `decide +kernel` does for decidable propositions,
and also works when the goal has free variables.
-/

namespace VG

open Lean Meta Elab Tactic in
/-- Proves `lhs = rhs` by `Eq.refl lhs`, which only the kernel checks. -/
elab "kernel_rfl" : tactic => liftMetaTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := ty.eq? | throwError "kernel_rfl: the goal is not an equation: {ty}"
  let u ← getLevel α
  let e ← mkAuxTheorem ty (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  g.assign e
  return []

end VG
