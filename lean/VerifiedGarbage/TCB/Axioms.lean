import Lean

/-!
# Axiom audit

**Trusted.** `#assert_standard_axioms c` fails unless the constant `c` (and so
everything it depends on, transitively) uses only Lean's three standard
axioms. In particular this rejects `sorry` (`sorryAx`) and anything proven by
`native_decide`/`bv_decide`, which rely on `Lean.ofReduceBool` and thus trust
the compiler.
-/

namespace VG

open Lean Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (!standardAxioms.contains ·)
  unless bad.isEmpty do
    throwError m!"{n} depends on non-standard axioms: {bad.toList}"
  logInfo m!"{n} depends only on the standard axioms {axs.toList}"

end VG
