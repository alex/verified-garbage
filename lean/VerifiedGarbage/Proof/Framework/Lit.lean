import Lean.Elab.Command
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Eval
import Lean.Util.ShareCommon
import VerifiedGarbage.TCB.Code

/-!
# Code as literals, for the kernel

The kernel evaluates code (the constant-time analysis, `Artifact.spSafe`, and
checks of every instruction), and most of that time can go into building the
instruction lists, which the code builds with functions (`List.append`,
`flatMap`, the round functions...), each structurally recursive: more than
the checks themselves, and again in every module that evaluates the code.

`materialize_code foo` evaluates `foo` (in compiled code) and defines
`foo.lit`, the same code written out as a literal, and
`foo.lit_eq : foo = foo.lit`, which the kernel checks once, by evaluation.
A proof about `foo.lit` is then a proof about `foo`. Code that calls a
function already materialized (`.call n g` with `g.lit` defined) refers to
`g.lit` rather than repeating it, so the kernel checks the callee's
instructions once for every caller (in `g.lit_eq`).

`lit_decide` proves a goal by `decide +kernel` after rewriting the code in
it that has a literal (`rw_lit`); `taint_decide` does the same.
-/

namespace VG

deriving instance Lean.ToExpr for Code

open Lean Meta Elab Command

namespace Lit

/-- The functions `materialize_code` has materialized, whose literals the
literals of their callers refer to: each `N` with a theorem `N.lit_eq`, in the
modules of this project (`VerifiedGarbage…`) and the current one. They are
found by name rather than recorded in an environment extension, whose
`initialize` the emitter's audit refuses (`TCB/Audit.lean`). -/
def litNames (env : Environment) : Array Name := Id.run do
  let add (acc : Array Name) (n : Name) : Array Name :=
    match n with
    | .str p "lit_eq" => if env.contains (.str p "lit") then acc.push p else acc
    | _ => acc
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if env.header.moduleNames[i].getRoot.toString.startsWith "VerifiedGarbage" then
      out := env.header.moduleData[i]!.constNames.foldl add out
  return env.constants.foldStage2 (fun acc n _ => add acc n) out

/-- Replaces each body of a call in `e` (a literal `Code`) that is the literal of a
materialized function by a free variable, returning the abstracted literal and the
functions, in the order of the free variables. -/
partial def abstractCalls (lits : Array (Name × Expr)) (e : Expr) :
    StateT (Array Name) MetaM Expr := do
  if e.isAppOfArity ``Code.call 4 then
    let body := e.appArg!
    for (g, v) in lits do
      if body == v then
        let gs ← get
        let i := (gs.findIdx? (· == g)).getD gs.size
        if i == gs.size then set (gs.push g)
        return mkApp (e.appFn!) (.bvar (1000000 + i))
  match e with
  | .app f a => return .app (← abstractCalls lits f) (← abstractCalls lits a)
  | _ => return e


/-- The literal `g.lit` written out in full: with the literal of each
materialized function it calls (`h.lit`) replaced by its own, in turn. This is
the value of `g`, as `materialize` evaluated it. -/
partial def expandLit (g : Name) : StateT (Std.HashMap Name Expr) MetaM Expr := do
  if let some e := (← get)[g]? then return e
  let env ← getEnv
  let some v := (env.find? (g ++ `lit)).bind (·.value?)
    | throwError "materialize_code: {g ++ `lit} has no value"
  let mut sub : Std.HashMap Name Expr := {}
  for c in v.getUsedConstants do
    if let .str p "lit" := c then
      if env.contains (.str p "lit_eq") then
        sub := sub.insert c (← expandLit p)
  let e := if sub.isEmpty then v else
    v.replace fun x => match x with
      | .const c _ => sub[c]?
      | _ => none
  modify (·.insert g e)
  return e

/-- The code `lhs` of `N.lit_eq : lhs = N.lit`. -/
def lhsOf (N : Name) : MetaM Expr := do
  let some (_, lhs, _) := (← getConstInfo (N ++ `lit_eq)).type.eq?
    | throwError "{N ++ `lit_eq} is not an equation"
  return lhs

/-- Defines `N.lit`, the value of the closed code term `code` as a literal
(calling the literals of the code materialized so far), and
`N.lit_eq : code = N.lit`. -/
def materialize (N : Name) (code : Expr) : MetaM Unit := do
  let ty ← inferType code
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do
    throwError "materialize_code: {code} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) codeTy)
  let eval (e : Expr) : MetaM Expr := unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) codeTy inst e)
  let v ← eval code
  -- The code materialized so far, written out in full.
  let mut lits : Array (Name × Expr) := #[]
  let mut expanded : Std.HashMap Name Expr := {}
  for g in litNames (← getEnv) do
    let lhs ← lhsOf g
    if (← isDefEq (← inferType lhs) ty) then
      let (e, m) ← (expandLit g).run expanded
      expanded := m
      lits := lits.push (g, e)
  let (abs, gs) ← (abstractCalls lits v).run #[]
  let lhss ← gs.mapM lhsOf
  -- `abs` with the `i`-th callee (marked `.bvar (1000000 + i)`) replaced by `f i`.
  let inst (f : Nat → Expr) : Expr :=
    abs.replace fun e => match e with
      | .bvar k => if 1000000 ≤ k then some (f (k - 1000000)) else none
      | _ => none
  let litV := ShareCommon.shareCommon' (inst fun i => mkConst (gs[i]! ++ `lit))
  addDecl <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := litV
    hints := .abbrev, safety := .safe }
  -- `code = abs[callees]` by evaluation, then each callee rewritten to its literal.
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty code rhs
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) ty code
  for i in [0:gs.size] do
    -- The code with the literals of the first `i` callees, and `x` for the `i`-th.
    let motive := Expr.lam `x ty
      (eqTy ((inst fun j => if j < i then mkConst (gs[j]! ++ `lit)
        else if j == i then .bvar 0 else lhss[j]!))) .default
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive lhss[i]!) (mkApp motive (mkConst (gs[i]! ++ `lit)))
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) lhss[i]!
        (mkConst (gs[i]! ++ `lit)) motive (mkConst (gs[i]! ++ `lit_eq))) prf
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
    value := ShareCommon.shareCommon' prf }

end Lit

open Lit in
/-- `materialize_code foo` defines `foo.lit`, the value of the code `foo` as a
literal (calling the literals of the code materialized before), and
`foo.lit_eq : foo = foo.lit`; `materialize_code N := t` does the same for the
closed code term `t`, as `N.lit` and `N.lit_eq`. -/
syntax "materialize_code " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_code $id:ident) => liftTermElabM do
    let foo ← realizeGlobalConstNoOverloadWithInfo id
    materialize foo (mkConst foo)
  | `(materialize_code $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_code: {e} is not closed"
    materialize ((← getCurrNamespace) ++ id.getId) e

open Elab Tactic Lit in
/-- Rewrites each code of the goal that has a literal (`materialize_code`) to it. -/
elab "rw_lit" : tactic => withMainContext do
  -- Only code whose head constant the goal mentions can occur in it.
  let used := (← instantiateMVars (← getMainTarget)).getUsedConstantsAsSet
  for N in litNames (← getEnv) do
    let lhs ← lhsOf N
    unless lhs.getAppFn.isConst && used.contains lhs.getAppFn.constName! do continue
    let tgt ← instantiateMVars (← getMainTarget)
    if (tgt.find? (· == lhs)).isNone then continue
    let g ← getMainGoal
    let r ← g.rewrite tgt (mkConst (N ++ `lit_eq))
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)

/-- `decide +kernel`, after rewriting the code constants of the goal to their
literals (`rw_lit`). -/
macro "lit_decide" : tactic => `(tactic| (rw_lit; decide +kernel))

end VG
