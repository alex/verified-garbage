import VerifiedGarbage.Proof.Framework.Taint

/-!
# Hints that forget what the rest of the code does not need

This only computes hints, which `Taint.check` checks.

`taint_decide_weak w` weakens the taints of a hint computed without `w`: it
can forget facts about memory, but not what the analysis derives from them
afterwards (a register loaded from a forgotten public word is still public
at the next hint), so `check` rejects the hint as soon as that happens.
`taint_decide_weaken w` instead weakens as it analyses: at every point where
the hint records a taint (every `chunk` instructions of a block, between the
parts of a `seq`, and each loop's invariant) the analysis continues from `w`
of it. The kernel's check then evaluates every instruction with the smaller
taints (e.g. without the public memory slots that only the caller's code
reads, inside a callee of thousands of instructions). A `w` that forgets too
much only makes the check fail.
-/

namespace VG.Taint

variable {M : ISA} (A : Taint M) (w : A.T → A.T)

/-- The hints for a block, weakened by `w`: the analysis after every `chunk`
instructions but the last, each continuing from the previous hint. -/
def chunkHintsW : A.T → List M.Instr → Nat → List A.T
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ chunk then [] else
    match A.checkBlock τ (is.take chunk) with
    | some τ' => w τ' :: chunkHintsW (w τ') (is.drop chunk) n
    | none => []

/-- `hint`, continuing from `w` of every taint it records. -/
def hintW : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is =>
    let ms := chunkHintsW A w τ is is.length
    (A.checkBlock (ms.getLast?.getD τ) (is.drop (chunk * ms.length))).map fun τ' => (τ', .block ms)
  | τ, .seq c₁ c₂ =>
    (hintW τ c₁).bind fun (τ₁, h₁) => (hintW (w τ₁) c₂).map fun (τ₂, h₂) => (τ₂, .seq (w τ₁) h₁ h₂)
  | τ, .ite _ t e =>
    (hintW τ t).bind fun (τ₁, h₁) => (hintW τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hintW · body) loopFuel (w τ)
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hintW τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hintW τ₁ body).bind fun (τ₂, h) => (A.pop τ₂ j).map (·, .frame h)
where
  go (c : M.Cond) (body : A.T → Option (A.T × Hint A.T)) :
      Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (w (A.meet σ σ'))

/-- The hint for `c` from `τ`, weakened by `w` (any hint, if the analysis fails). -/
def hintWOf (τ : A.T) (c : Prog M) : Hint A.T := ((hintW A w τ c).map (·.2)).getD (.block [])

end VG.Taint

namespace VG

open Lean Meta Elab Tactic in
/-- Proves `(Taint.check A τ c ?hint).isSome = true` (or any decidable
equation whose left side contains `Taint.check A τ c ?hint`), like
`taint_decide`, with the hint computed by `Taint.hintW A w`: the analysis
forgets, at every point the hint records, what `w : A.T → A.T` forgets. -/
elab "taint_decide_weaken " wt:term : tactic => do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_decide_weaken: the goal is not an equation about `Taint.check A τ c h`"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "taint_decide_weaken: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless h.isMVar do throwError "taint_decide_weaken: the hint is already given"
  let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
  let hty := mkApp (mkConst ``Taint.Hint) tT
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
  let wv ← Term.elabTermEnsuringType wt (← mkArrow tT tT)
  Term.synthesizeSyntheticMVarsNoPostponing
  let hint := mkApp5 (mkConst ``Taint.hintWOf) m a (← instantiateMVars wv) τ c
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst hint)
  h.mvarId!.assign hv
  -- The kernel evaluates the literal of any code that has one (`materialize_code`).
  evalTactic (← `(tactic| lit_decide))

end VG
