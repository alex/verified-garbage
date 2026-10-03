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
  -- (`moduleNames` builds the array on every use.)
  let mods := env.header.moduleNames
  for h : i in [0:mods.size] do
    if mods[i].getRoot.toString.startsWith "VerifiedGarbage" then
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

/-- The constants `c` with a literal (`c.lit_eq : c = c.lit`), from
`materialize_code c` or `materialize_table c`. -/
def litConsts (env : Environment) : Array Name :=
  (litNames env).filter fun N => match env.find? (N ++ `lit_eq) with
    | some ci => match ci.type.eq? with
      | some (_, .const c _, _) => c == N
      | _ => false
    | none => false

/-- Whether `S` is a structure with a field that is a proof. -/
def hasProofFields (S : Expr) : MetaM Bool := do
  let .const S _ := S | return false
  let env ← getEnv
  unless isStructure env S do return false
  forallTelescopeReducing (getStructureCtor env S).type fun xs _ =>
    xs.anyM fun x => do isProp (← inferType x)

/-- Whether `c` is from a module that builds code (or the current module):
not the trusted base, the specifications or this framework, whose
definitions (the ISA models, ...) never lead to code with a literal, and
which `reaches` would otherwise search on every call. -/
def codeModule (env : Environment) (mods : Array Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i => match mods[i.toNat]?.map (·.components) with
    | some (`VerifiedGarbage :: `Proof :: `Framework :: _) => false
    | some (`VerifiedGarbage :: k :: _) => k ∈ [`Impl, `Proof, `Variants, `Generic, `Artifacts]
    | _ => false

/-- Whether the definition `c` uses one of `targets`, directly or through
definitions of this project, memoized in the state. -/
partial def reaches (targets : NameSet) (mods : Array Name) (c : Name) :
    StateT (NameMap Bool) MetaM Bool := do
  if let some b := (← get).find? c then return b
  modify (·.insert c false)
  let env ← getEnv
  unless codeModule env mods c do return false
  let some (.defnInfo d) := env.find? c | return false
  -- Only data: unfolding a proposition could hide its `Decidable` instance.
  if d.type.getForallBody.isProp then return false
  let mut r := false
  -- Every constant used is visited (no early exit): `unfoldWhere` unfolds
  -- exactly the constants memoized as reaching, so stopping at the first one
  -- would leave the others (e.g. the second of two calls to code with a
  -- literal) folded, and the kernel would evaluate them again.
  for u in d.value.getUsedConstants do
    if targets.contains u then r := true
    else if u.getRoot == `VG && !(u matches .str _ "lit") then
      if ← reaches targets mods u then r := true
  -- Rewriting code inside a structure with proofs about it would change the
  -- types of those proofs.
  if r then r := !(← hasProofFields d.type.getForallBody.getAppFn)
  modify (·.insert c r)
  return r

/-- `e` with the applications of the constants `p` holds of unfolded, again
in what they unfold to. A plain `Expr.replace`, which visits each shared
subterm once: the goals of `rw_lit` carry large literals (a hint of
`taint_decide`) that have nothing to unfold. -/
partial def unfoldWhere (env : Environment) (p : Name → Bool) (e : Expr)
    (stop : Expr → Bool := fun _ => false) : Expr :=
  e.replace fun t => if stop t then some t else match t.getAppFn with
    | .const c ls =>
      if p c then match env.find? c with
        | some (.defnInfo d) =>
          some (unfoldWhere env p ((d.value.instantiateLevelParams d.levelParams ls).betaRev
            t.getAppRevArgs) stop)
        | _ => none
      else none
    | _ => none

/-- The maximal closed subterms of `e` whose head is a definition that leads
to constants with a literal (`reaches`), or one of them. -/
def reachingSubterms (e : Expr) : MetaM (Array Expr) := do
  let targets := (litConsts (← getEnv)).foldl (fun s c => s.insert c) ({} : NameSet)
  if targets.isEmpty then return #[]
  let mods := (← getEnv).header.moduleNames
  let mut memo : NameMap Bool := {}
  for u in e.getUsedConstants do
    if !targets.contains u then
      (_, memo) ← (reaches targets mods u).run memo
  let memo' := memo
  let hit (c : Name) := targets.contains c || memo'.find? c == some true
  unless e.getUsedConstants.any hit do return #[]
  let rec go (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
    if (← get).1.contains e then return
    modify fun (v, out) => (v.insert e, out)
    match e.getAppFn with
    | .const c _ =>
      if hit c && !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
        modify fun (v, out) => (v, out.push e)
        return
    | _ => pure ()
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  let ((), (_, out)) := (go e).run ({}, #[])
  return out

/-- For `x` (code, or a goal), a proof of `x = x'` and `x'`, where `x'` is `x`
with the definitions that lead to constants with a literal (but `N`)
unfolded, and those constants replaced by their literals; `none` if `x`
reaches none. The kernel checks the unfolding by delta reduction alone, and
then, evaluating `x'`, reads each literal rather than running again the
functions it was evaluated from: functions that build code (a register
allocator, tables of constants) are evaluated once, in their own `lit_eq`,
rather than in every literal or check of the code that uses them. -/
def unfoldToLits (N : Name) (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let targets := (litConsts env).foldl (fun s c => if c == N then s else s.insert c) {}
  -- The code with a literal that is an application (`materialize_code M := f a`):
  -- its occurrences are rewritten to `M.lit` as a whole (and not unfolded), so
  -- the definitions that lead to `f` are unfolded too.
  let mut atoms : Array (Name × Expr) := #[]
  for M in litNames env do
    if M == N || targets.contains M then continue
    let lhs ← lhsOf M
    if lhs.getAppFn.isConst && !lhs.hasLooseBVars && !lhs.hasFVar && !lhs.hasMVar then
      atoms := atoms.push (M, lhs)
  let heads := atoms.foldl (fun s (_, l) => s.insert l.getAppFn.constName!) ({} : NameSet)
  let reachT := heads.foldl (fun s c => s.insert c) targets
  if reachT.isEmpty then return none
  let consts := x.getUsedConstants
  let mods := env.header.moduleNames
  let mut memo : NameMap Bool := {}
  for u in consts do
    if !reachT.contains u then
      (_, memo) ← (reaches reachT mods u).run memo
  unless memo.any (fun _ b => b) || consts.any reachT.contains do return none
  -- The heads of the applications are unfolded where they are not one of
  -- them, if they lead to constants with a literal (or other applications).
  let mut headReach : NameSet := {}
  for c in heads do
    let some (.defnInfo d) := env.find? c | continue
    if !codeModule env mods c || d.type.getForallBody.isProp then continue
    let mut r := false
    for v in d.value.getUsedConstants do
      if reachT.contains v then r := true
      else if v.getRoot == `VG && !(v matches .str _ "lit") then
        let (b, m) ← (reaches reachT mods v).run memo
        memo := m
        if b then r := true
    if r && !(← hasProofFields d.type.getForallBody.getAppFn) then headReach := headReach.insert c
  let memo' := memo
  let headReach' := headReach
  let isAtom (t : Expr) : Bool :=
    t.getAppFn.isConst && heads.contains t.getAppFn.constName! && atoms.any (·.2 == t)
  let e := unfoldWhere env (fun c => memo'.find? c == some true || headReach'.contains c) x isAtom
  -- What is rewritten to a literal: the constants with one, then the applications.
  let mut items : Array (Expr × Name) :=
    (e.getUsedConstants.filter targets.contains).map fun c => (mkConst c, c)
  for (M, lhs) in atoms do
    if (e.find? (· == lhs)).isSome then items := items.push (lhs, M)
  if items.isEmpty then return none
  let ty ← inferType x
  let u ← getLevel ty
  let itemIdx (t : Expr) : Option Nat := items.findIdx? fun (pat, _) => match pat, t with
    | .const c _, .const c' _ => c == c'
    | pat, t => !pat.isConst && pat == t
  -- `e` with the `j`-th item replaced by its literal for `j < k`, and by `y`
  -- for `j = k`; later items are left as they are (and not looked into).
  let inst (k : Nat) (y : Option Expr) : Expr :=
    e.replace fun t => match itemIdx t with
      | some j => if j < k then some (mkConst (items[j]!.2 ++ `lit))
          else if j == k then y else some t
      | none => none
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [u]) ty x rhs
  -- `x = e` by delta, then each item rewritten to its literal.
  let mut prf := mkApp2 (mkConst ``Eq.refl [u]) ty x
  for h : k in [0:items.size] do
    let (pat, M) := items[k]
    let cty ← inferType pat
    let lvl ← getLevel cty
    let motive ← withLocalDeclD `y cty fun y => mkLambdaFVars #[y] (eqTy (inst k (some y)))
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive pat) (mkApp motive (mkConst (M ++ `lit)))
      (mkApp6 (mkConst ``congrArg [lvl, 1]) cty (mkSort 0) pat
        (mkConst (M ++ `lit)) motive (mkConst (M ++ `lit_eq))) prf
  return some (inst items.size none, prf)

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
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty code rhs
  -- If the code reaches literals: `code = e'` by unfolding (`unfoldToLits`),
  -- and `e' = N.lit` by evaluation.
  if let some (_, prf) ← unfoldToLits N code then
    addDecl <| .thmDecl {
      name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
      value := ShareCommon.shareCommon' prf }
    return
  -- `code = abs[callees]` by evaluation, then each callee rewritten to its literal.
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

/-- A function on `Nat` is the table of its first values, falling back to
itself beyond them. -/
theorem Lit.table_eq {α : Type} (f : Nat → α) (n : Nat) (l : List α)
    (h : (List.range n).map f = l) : f = fun i => l.getD i (f i) := by
  funext i
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function of two `Nat`s is the table of its first values, falling back
to itself beyond them. -/
theorem Lit.table2_eq {α : Type} (f : Nat → Nat → α) (n m : Nat) (l : List (List α))
    (h : (List.range n).map (fun i => (List.range m).map (f i)) = l) :
    f = fun i j => (l.getD i []).getD j (f i j) := by
  funext i j
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi, Option.map_some, Option.getD_some, List.getElem?_map]
    by_cases hj : j < m
    · rw [List.getElem?_range hj]; rfl
    · rw [List.getElem?_eq_none (by simpa using hj)]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function to `Nat` is its first values packed in `w`-bit fields of one
number `N` (`M = 2 ^ w`), falling back to itself beyond them: the kernel
reads a value with two arithmetic operations, which it runs natively,
rather than walking a list. -/
theorem Lit.packed_eq (f : Nat → Nat) (n w M N : Nat)
    (h : (List.range n).all (fun i => Nat.beq (N >>> (w * i) % M) (f i)) = true) :
    f = fun i => cond (Nat.blt i n) (N >>> (w * i) % M) (f i) := by
  funext i
  cases hi : Nat.blt i n
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))).symm

/-- `Lit.packed_eq` for a function of two `Nat`s, its values at `i < n`,
`j < m` in field `m i + j`. -/
theorem Lit.packed2_eq (f : Nat → Nat → Nat) (n m w M N : Nat)
    (h : (List.range n).all (fun i => (List.range m).all fun j =>
      Nat.beq (N >>> (w * (m * i + j)) % M) (f i j)) = true) :
    f = fun i j => cond (Nat.blt i n && Nat.blt j m) (N >>> (w * (m * i + j)) % M) (f i j) := by
  funext i j
  cases hi : Nat.blt i n <;> cases hj : Nat.blt j m
  · rfl
  · rfl
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    have hj : j < m := Nat.blt_eq.mp hj
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j
      (List.mem_range.mpr hj))).symm

open Lit in
/-- `materialize_table f n`, for a closed `f : Nat → α`, defines `f.lit`, the
table of the values `f 0`, …, `f (n - 1)` as literals (and `f i` beyond
them), and `f.lit_eq : f = f.lit`, which the kernel checks by evaluating
those `n` values once. The literals of code that calls `f` then read the
table (`materialize_code`). `materialize_table f n m`, for a closed
`f : Nat → Nat → α`, does the same with the table of the values `f i j`,
`i < n`, `j < m`. A table of `Nat`s is one number (`Lit.packed_eq`), which
the kernel reads in constant time; others are lists. -/
elab "materialize_table " id:ident n:num m:(num)? : command => liftTermElabM do
  let f ← realizeGlobalConstNoOverloadWithInfo id
  let fty ← whnfD (← inferType (mkConst f))
  let .forallE _ (.const ``Nat []) α _ := fty
    | throwError "materialize_table: {f} is not a function on `Nat`: {fty}"
  if α.hasLooseBVars then throwError "materialize_table: {f} is dependent"
  let nat := mkConst ``Nat
  let range (k : Nat) := mkApp (mkConst ``List.range) (mkNatLit k)
  -- The values of the table (the type of its rows, and the values of `g`), and
  -- the value of `g` at `i` (and `j`) from the table `l`, else `d`.
  let (β, rowTy, valsOf, lookup) ← match m with
    | none => pure (α, α,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat α g (range n.getNat),
        fun (l i _ d : Expr) => mkApp4 (mkConst ``List.getD [0]) α l i d)
    | some m =>
      let .forallE _ (.const ``Nat []) β _ ← whnfD α
        | throwError "materialize_table: {f} is not a function of two `Nat`s: {fty}"
      if β.hasLooseBVars then throwError "materialize_table: {f} is dependent"
      let rowTy := mkApp (mkConst ``List [0]) β
      pure (β, rowTy,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat rowTy
          (.lam `i nat (mkApp4 (mkConst ``List.map [0, 0]) nat β (mkApp g (.bvar 0)) (range m.getNat)) .default)
          (range n.getNat),
        fun (l i j d : Expr) => mkApp4 (mkConst ``List.getD [0]) β
          (mkApp4 (mkConst ``List.getD [0]) rowTy l i (mkApp (mkConst ``List.nil [0]) β)) j d)
  let listTy := mkApp (mkConst ``List [0]) rowTy
  -- A table of `Nat`s is packed in one number (`Lit.packed_eq`).
  if β == nat then
    let vals : List Nat ← match m with
      | none => unsafe evalExpr (List Nat) (mkApp (mkConst ``List [0]) nat) (valsOf (mkConst f))
      | some _ => do
        let rows ← unsafe evalExpr (List (List Nat)) listTy (valsOf (mkConst f))
        pure rows.flatten
    let w := max 1 (vals.foldl (fun w v => max w v.log2.succ) 0)
    let N := vals.foldr (fun v acc => v ||| (acc <<< w)) 0
    let lemma (g : Expr) : Expr := match m with
      | none => mkApp5 (mkConst ``Lit.packed_eq) g (mkNatLit n.getNat) (mkNatLit w) (mkNatLit (2 ^ w))
          (mkNatLit N)
      | some m => mkApp6 (mkConst ``Lit.packed2_eq) g (mkNatLit n.getNat) (mkNatLit m.getNat) (mkNatLit w)
          (mkNatLit (2 ^ w)) (mkNatLit N)
    -- The hypothesis of the lemma, for `g`: its values are the table's.
    let hTyOf (g : Expr) : MetaM Expr := do return (← whnfR (← inferType (lemma g))).bindingDomain!
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    -- By evaluation, of `f` with the literals it reaches (`unfoldToLits`) if any.
    let h ← match ← unfoldToLits f (mkConst f) with
      | none => pure refl
      | some (f', prfF) =>
        let motive ← withLocalDeclD `g fty fun g => do mkLambdaFVars #[g] (← hTyOf g)
        pure <| mkApp4 (mkConst ``Eq.mpr [0]) (← hTyOf (mkConst f)) (← hTyOf f')
          (mkApp6 (mkConst ``congrArg [1, 1]) fty (mkSort 0) (mkConst f) f' motive prfF) refl
    let prf := mkApp (lemma (mkConst f)) h
    let some (_, _, litV) := (← inferType prf).eq?
      | throwError "materialize_table: unexpected {← inferType prf}"
    addDecl <| .defnDecl {
      name := f ++ `lit, levelParams := [], type := fty, value := litV
      hints := .abbrev, safety := .safe }
    addDecl <| .thmDecl {
      name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
      value := prf }
    return
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) listTy)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) listTy inst
    (valsOf (mkConst f)))
  let l := ShareCommon.shareCommon' l
  -- `valsOf f = l`: by evaluation, of `f` with the literals it reaches
  -- (`unfoldToLits`) if any, so that a table built from tables reads them.
  let refl := mkApp2 (mkConst ``Eq.refl [1]) listTy l
  let hvals ← match ← unfoldToLits f (mkConst f) with
    | none => pure refl
    | some (f', prfF) =>
      let motive ← withLocalDeclD `g fty fun g => mkLambdaFVars #[g] (valsOf g)
      pure <| mkApp6 (mkConst ``Eq.trans [1]) listTy (valsOf (mkConst f)) (valsOf f') l
        (mkApp6 (mkConst ``congrArg [1, 1]) fty listTy (mkConst f) f' motive prfF) refl
  let litV ← match m with
    | none => withLocalDeclD `i nat fun i =>
        mkLambdaFVars #[i] (lookup l i i (mkApp (mkConst f) i))
    | some _ => withLocalDeclD `i nat fun i => withLocalDeclD `j nat fun j =>
        mkLambdaFVars #[i, j] (lookup l i j (mkApp2 (mkConst f) i j))
  let prf := match m with
    | none => mkApp5 (mkConst ``Lit.table_eq) β (mkConst f) (mkNatLit n.getNat) l hvals
    | some m => mkApp6 (mkConst ``Lit.table2_eq) β (mkConst f) (mkNatLit n.getNat) (mkNatLit m.getNat) l hvals
  addDecl <| .defnDecl {
    name := f ++ `lit, levelParams := [], type := fty, value := litV
    hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl {
    name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
    value := ShareCommon.shareCommon' prf }

namespace Lit

/-- Defines `N.lit`, the value of the closed term `v` (of a type with a
`ToExpr` instance) as a literal, and `N.lit_eq : v = N.lit`, by evaluation
(reading the literals `v` reaches). -/
def materializeValue (N : Name) (v : Expr) : MetaM Unit := do
  let ty ← instantiateMVars (← inferType v)
  if ty.hasLevelParam || ty.hasMVar then throwError "materialize_value: {v} is universe polymorphic"
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst v)
  addDecl <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
    hints := .abbrev, safety := .safe }
  -- By evaluation, of `v` with the literals it reaches (`unfoldToLits`) if any.
  let prf ← match ← unfoldToLits N v with
    | some (_, prf) => pure prf
    | none => pure (mkApp2 (mkConst ``Eq.refl [1]) ty v)
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty v (mkConst (N ++ `lit))
    value := ShareCommon.shareCommon' prf }

end Lit

open Lit in
/-- `materialize_value c`, for a closed constant `c` whose type has a `ToExpr`
instance (e.g. a list of instructions that several programs contain),
defines `c.lit`, its value as a literal, and `c.lit_eq : c = c.lit`, which the
kernel checks once, by evaluation; `materialize_value N := t` does the same for
the closed term `t`, as `N.lit` and `N.lit_eq`. The literals of code that
contains it then read it (`materialize_code`), as for `materialize_table`. -/
syntax "materialize_value " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_value $id:ident) => liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    unless (← getConstInfo c).levelParams.isEmpty do
      throwError "materialize_value: {c} is universe polymorphic"
    materializeValue c (mkConst c)
  | `(materialize_value $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_value: {e} is not closed"
    materializeValue ((← getCurrNamespace) ++ id.getId) e

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
  -- The definitions of the goal that lead to constants with a literal
  -- (`materialize_table`, code used other than as a call), unfolded, and
  -- those constants rewritten to their literals.
  -- Each is rewritten on its own, and then in the goal with one `congrArg`:
  -- the goal can be large (a hint of `taint_decide`), and the kernel
  -- instantiates the motive of each rewrite of it.
  let tgt ← instantiateMVars (← getMainTarget)
  for s in ← reachingSubterms tgt do
    let some (s', prf) ← unfoldToLits .anonymous s | continue
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let ty ← inferType s
    let motive ← withLocalDeclD `y ty fun y =>
      mkLambdaFVars #[y] (tgt.replace fun t => if t == s then some y else none)
    let eqPrf := mkApp6 (mkConst ``congrArg [← getLevel ty, 1]) ty (mkSort 0) s s' motive prf
    replaceMainGoal [← g.replaceTargetEq (tgt.replace fun t => if t == s then some s' else none) eqPrf]

/-- `decide +kernel`, after rewriting the code constants of the goal to their
literals (`rw_lit`). -/
macro "lit_decide" : tactic => `(tactic| (rw_lit; decide +kernel))

end VG
