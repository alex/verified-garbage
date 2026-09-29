import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Omega

/-!
# `omega` in large contexts

Untrusted: this only changes how proofs are found.

`omega` and `bv_omega` use every hypothesis in the local context (`bv_omega`
first rewrites every one of them with `simp … at *`). In the middle of a long
proof about machine states most hypotheses are facts about memory, regions
or states that they cannot use, and looking at them costs a tenth of a second
or more per call; and preprocessing each fact about `/` and `%` introduces
new variables and constraints, which every call pays for and the kernel
checks. Two ways to run them on less:

* `omega_arith` and `bv_omega_arith` first clear every hypothesis that is not
  an (in)equation between natural numbers, integers or bit vectors, or a
  propositional combination of such (they cannot use any other);
* `omega_using [h₁, …, hₙ]` and `bv_omega_using [h₁, …, hₙ]` use only the
  facts `h₁, …, hₙ` (any terms), with every other hypothesis cleared.
-/

namespace VG.Omega

open Lean Meta Elab Tactic

/-- Whether `e` is a type `omega` reasons about: `Nat`, `Int`, `Fin n` or `BitVec w`. -/
def isArithType (e : Expr) : Bool :=
  e.isConstOf ``Nat || e.isConstOf ``Int || e.isAppOfArity ``BitVec 1 || e.isConstOf ``Fin ||
    e.isAppOfArity ``Fin 1

/-- Whether `p` is a fact `omega` may use: (in)equations over `Nat`, `Int` or
`BitVec`, `Dvd`, and `¬`, `∧`, `∨`, `↔`, `→` of those. -/
partial def isArithProp (p : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  match p.getAppFn.constName?, p.getAppNumArgs with
  | some ``Eq, 3 | some ``Ne, 3 | some ``LE.le, 4 | some ``LT.lt, 4 | some ``GE.ge, 4
  | some ``GT.gt, 4 | some ``Dvd.dvd, 4 => return isArithType (p.getArg! 0)
  | some ``Not, 1 => isArithProp (p.getArg! 0)
  | some ``And, 2 | some ``Or, 2 | some ``Iff, 2 =>
    return (← isArithProp (p.getArg! 0)) && (← isArithProp (p.getArg! 1))
  | _, _ =>
    if p.isArrow then return (← isArithProp p.bindingDomain!) && (← isArithProp p.bindingBody!)
    else return p.isConstOf ``False || p.isConstOf ``True

/-- Clears every hypothesis `omega` cannot use (and that nothing else depends on). -/
def clearNonArith : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).getFVarIds.reverse do
    let some ld := (← getLCtx).find? d | continue
    if ld.isImplementationDetail || ld.isLet then continue
    let ty ← instantiateMVars ld.type
    unless ← isProp ty do continue
    if ← isArithProp ty then continue
    try g ← g.clear d catch _ => pure ()
  replaceMainGoal [g]

/-- Adds the facts `hs` to the main goal as new hypotheses, and clears every
other hypothesis that is a proposition. -/
def keepOnly (hs : Array Term) : TacticM Unit := do
  let mut g ← getMainGoal
  -- Elaborate every fact in the original context, then add them as new hypotheses.
  let facts ← g.withContext do
    hs.mapM fun h => do
      let e ← Term.elabTerm h none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      pure (e, ← instantiateMVars (← inferType e))
  let mut keep : Array FVarId := #[]
  for (e, ty) in facts do
    let (fv, g') ← (← g.assert (← mkFreshUserName `h) ty e).intro1P
    keep := keep.push fv
    g := g'
  let g' ← g.withContext do
    let mut g := g
    for fv in (← getLCtx).getFVarIds.reverse do
      if keep.contains fv then continue
      let d ← fv.getDecl
      if d.isImplementationDetail then continue
      if ← isProp d.type then
        g ← g.tryClear fv
    pure g
  replaceMainGoal [g']

/-- Clears every hypothesis `omega` cannot use. -/
elab "clear_non_arith" : tactic => clearNonArith

/-- `omega` using only the given facts, not the local context. -/
syntax (name := omegaUsing) "omega_using " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| omega_using [$hs,*]) => do
    keepOnly hs.getElems
    evalTactic (← `(tactic| omega))

/-- `bv_omega` using only the given facts, not the local context. -/
syntax (name := bvOmegaUsing) "bv_omega_using " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| bv_omega_using [$hs,*]) => do
    keepOnly hs.getElems
    evalTactic (← `(tactic| bv_omega))

end VG.Omega

/-- `omega`, after clearing the hypotheses it cannot use. -/
macro "omega_arith" : tactic => `(tactic| (clear_non_arith; omega))

/-- `bv_omega`, after clearing the hypotheses it cannot use. -/
macro "bv_omega_arith" : tactic => `(tactic| (clear_non_arith; bv_omega))

/-- `decide` if the goal is about numerals only (as the side conditions of
lemmas about literal offsets are, once instantiated), and `omega` otherwise.
`omega` first collects every arithmetic hypothesis in the context, a tenth of
a second or more deep in a proof about states; `decide` does not look at the
context. -/
macro "lit_omega" : tactic => `(tactic| first | decide | omega)
