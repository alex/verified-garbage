import Lean.Elab.Tactic.Omega

/-!
# `omega` on closed goals

Untrusted: this only changes how proofs are found.

`omega` builds a certificate for its goal, which the kernel then checks: a
tenth of a second or so per call, even when the goal is about literals only
(such as `3 < 7` or `176 + 4 ≤ 240`, side conditions of lemmas about
offsets). `omega_nat` proves a goal without free variables by `decide`,
which the kernel evaluates with its native arithmetic, and any other goal (or
one `decide` cannot prove, such as `False` from contradictory hypotheses) by
`omega`.
-/

namespace VG.OmegaLit

open Lean Meta Elab Tactic

/-- `decide` if the goal has no free variables and holds, `omega` otherwise. -/
elab "omega_nat" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then
    evalTactic (← `(tactic| omega))
  else
    evalTactic (← `(tactic| first | decide | omega))

end VG.OmegaLit
