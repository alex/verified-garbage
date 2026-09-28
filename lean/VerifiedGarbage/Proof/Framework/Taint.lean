import VerifiedGarbage.Proof.Framework.Semantics
import Lean.Elab.Tactic

/-!
# Constant time by taint tracking

Untrusted: everything here is checked by Lean.

A `Taint M` is a sound, executable information-flow analysis for the ISA `M`:
an abstract domain `T` of "which parts of the state are public", a relation
`Agree τ s₁ s₂` ("the two states agree on everything `τ` says is public"),
and a transfer function for instructions that fails (`none`) whenever an
instruction would leak (through the addresses it accesses) something that is
not public. `Taint.check` lifts it to structured code; `Taint.constantTime`
turns a successful check into `ConstantTime`, which can then be established
for a whole program by evaluation (`taint_decide`).

The kernel is a slow evaluator, so `check` does not search for loop
invariants itself: it is given a `Hint` with every loop's invariant, and the
analysis at every `seq` and every `chunk` instructions of a block, and only
checks that they are sound (`le`). `Taint.hint` computes such a hint by
running the search in compiled code, and `taint_decide` has the kernel check
the analysis with it. A wrong hint can only make the check fail.
-/

namespace VG

structure Taint (M : ISA) where
  T : Type
  Agree : T → M.State → M.State → Prop
  step : T → M.Instr → Option T
  step_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → step τ i = some τ' →
    M.exec i s₁ = some s₁' → M.exec i s₂ = some s₂' →
    M.addrs i s₁ = M.addrs i s₂ ∧ Agree τ' s₁' s₂'
  /-- The condition only depends on public data. -/
  condPub : T → M.Cond → Bool
  cond_sound : ∀ {τ c s₁ s₂}, Agree τ s₁ s₂ → condPub τ c = true → M.eval c s₁ = M.eval c s₂
  /-- Something public in both. -/
  meet : T → T → T
  meet_left : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₁ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  meet_right : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₂ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  /-- `le τ σ`: everything public in `τ` is public in `σ`. -/
  le : T → T → Bool
  le_sound : ∀ {τ σ s₁ s₂}, le τ σ = true → Agree σ s₁ s₂ → Agree τ s₁ s₂
  /-- The analysis of a call instruction (`none` if it would leak). -/
  call : T → Option T
  call_sound : ∀ {τ τ' s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → call τ = some τ' →
    M.call s₁ = some s₁' → M.call s₂ = some s₂' → M.callAddrs s₁ = M.callAddrs s₂ ∧ Agree τ' s₁' s₂'
  /-- The analysis of a called function's return instruction. -/
  ret : T → Option T
  ret_sound : ∀ {τ τ' a₁ a₂ b₁ b₂ c₁ c₂}, Agree τ b₁ b₂ → ret τ = some τ' →
    M.ret a₁ b₁ = some c₁ → M.ret a₂ b₂ = some c₂ → M.retAddrs b₁ = M.retAddrs b₂ ∧ Agree τ' c₁ c₂

namespace Taint

/-- Precomputed results of the analysis, for `check`: the taint at every
`chunk` instructions of a block and between the parts of a `seq`, and every
loop's invariant. -/
inductive Hint (T : Type) where
  | block (mids : List T)
  | seq (mid : T) (h₁ h₂ : Hint T)
  | ite (h₁ h₂ : Hint T)
  | loop (inv : T) (h : Hint T)
  | call (h : Hint T)
  deriving Lean.ToExpr

variable {M : ISA} (A : Taint M)

def checkBlock : A.T → List M.Instr → Option A.T
  | τ, [] => some τ
  | τ, i :: is => (A.step τ i).bind fun τ' => checkBlock τ' is

/-- How many instructions of a block `check` analyses between hints. -/
def chunk : Nat := 64

/-- The analysis of a block, weakened to `mids` after every `chunk` instructions. -/
def checkChunks : A.T → List M.Instr → List A.T → Option A.T
  | τ, is, [] => A.checkBlock τ is
  | τ, is, m :: ms => (A.checkBlock τ (is.take chunk)).bind fun τ' =>
    if A.le m τ' then checkChunks m (is.drop chunk) ms else none

/-- The analysis of structured code, given a hint. -/
def check : A.T → Prog M → Hint A.T → Option A.T
  | τ, .block is, .block ms => checkChunks A τ is ms
  | τ, .seq c₁ c₂, .seq mid h₁ h₂ =>
    (check τ c₁ h₁).bind fun τ' => if A.le mid τ' then check mid c₂ h₂ else none
  | τ, .ite c t e, .ite h₁ h₂ =>
    if A.condPub τ c then
      (check τ t h₁).bind fun τ₁ => (check τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | τ, .loop body c, .loop σ h =>
    if A.le σ τ then
      (check σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | τ, .call _ body, .call h => (A.call τ).bind fun τ₁ => (check τ₁ body h).bind A.ret
  | _, _, _ => none

/-! ## Computing hints

Nothing here needs to be sound: `check` checks the hint. -/

/-- The hints for a block: the analysis after every `chunk` instructions but the last. -/
def chunkHints : A.T → List M.Instr → Nat → List A.T
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ chunk then [] else
    match A.checkBlock τ (is.take chunk) with
    | some τ' => τ' :: chunkHints τ' (is.drop chunk) n
    | none => []

/-- How many times the search for a loop invariant weakens its candidate. -/
def loopFuel : Nat := 4

/-- The analysis of structured code, with its hint. A loop's invariant is
found by starting from the taint on entry and, while the body does not keep
public everything the candidate says is public (or leaves the loop condition
secret), weakening the candidate to what is public both before and after the
body. -/
def hint : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A τ is is.length))
  | τ, .seq c₁ c₂ =>
    (hint τ c₁).bind fun (τ₁, h₁) => (hint τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hint τ t).bind fun (τ₁, h₁) => (hint τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hint · body) loopFuel τ
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hint τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | _, .frame .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × Hint A.T)) :
      Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The hint for `c` from `τ` (any hint, if the analysis fails). -/
def hintOf (τ : A.T) (c : Prog M) : Hint A.T := ((hint A τ c).map (·.2)).getD (.block [])

/-! ## Soundness -/

variable {A}

theorem checkBlock_sound {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : execBlock M is s₁ = some (s₁', t₁)) (e₂ : execBlock M is s₂ = some (s₂', t₂)) :
    t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction is generalizing τ s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂; subst h; exact ⟨rfl, ha⟩
  | cons i is ih =>
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> rename_i h₁ <;> [cases e₁; skip]
    split at e₂ <;> rename_i h₂ <;> [cases e₂; skip]
    rename_i s₁₁ _ s₂₁
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, e₁, he₁⟩ := e₁
    obtain ⟨_, u₂, e₂, he₂⟩ := e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    obtain ⟨hadd, ha₁⟩ := A.step_sound ha hs h₁ h₂
    obtain ⟨ht, ha'⟩ := ih hr ha₁ e₁ e₂
    exact ⟨by rw [hadd, ht], ha'⟩

theorem execBlock_split {is : List M.Instr} {s s' : M.State} {t : List Leak} (n : Nat)
    (e : execBlock M is s = some (s', t)) :
    ∃ s₁ u₁ u₂, execBlock M (is.take n) s = some (s₁, u₁) ∧
      execBlock M (is.drop n) s₁ = some (s', u₂) ∧ t = u₁ ++ u₂ := by
  rw [← List.take_append_drop n is, execBlock_append] at e
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at e
  obtain ⟨⟨s₁, u₁⟩, e₁, ⟨s₂, u₂⟩, e₂, rfl, rfl⟩ := e
  exact ⟨s₁, u₁, u₂, e₁, e₂, rfl⟩

theorem checkChunks_sound {ms : List A.T} {is : List M.Instr} {τ τ' : A.T}
    {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak} (h : A.checkChunks τ is ms = some τ')
    (ha : A.Agree τ s₁ s₂) (e₁ : execBlock M is s₁ = some (s₁', t₁))
    (e₂ : execBlock M is s₂ = some (s₂', t₂)) : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction ms generalizing τ is s₁ s₂ t₁ t₂ with
  | nil => exact checkBlock_sound h ha e₁ e₂
  | cons m ms ih =>
    simp only [checkChunks, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hle; cases h₂]
    obtain ⟨_, _, _, a₁, b₁, rfl⟩ := execBlock_split chunk e₁
    obtain ⟨_, _, _, a₂, b₂, rfl⟩ := execBlock_split chunk e₂
    obtain ⟨rfl, ha₁⟩ := checkBlock_sound h₁ ha a₁ a₂
    obtain ⟨rfl, ha₂⟩ := ih h₂ (A.le_sound hle ha₁) b₁ b₂
    exact ⟨rfl, ha₂⟩

theorem check_sound {c : Prog M} {τ τ' : A.T} {hc : Hint A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (h : A.check τ c hc = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂') : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction e₁ generalizing τ τ' hc s₂ t₂ s₂' with
  | block h₁ =>
    cases hc <;> simp only [check, reduceCtorEq] at h
    cases e₂ with
    | block h₂ => exact checkChunks_sound h ha h₁ h₂
  | seq _ _ ih₁ ih₂ =>
    cases hc <;> simp only [check, reduceCtorEq] at h
    cases e₂ with
    | seq a b =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hle; cases h₂]
      obtain ⟨rfl, ha₁⟩ := ih₁ h₁ ha a
      obtain ⟨rfl, ha₂⟩ := ih₂ h₂ (A.le_sound hle ha₁) b
      exact ⟨rfl, ha₂⟩
  | iteT hc' _ ih =>
    cases hc <;> simp only [check, reduceCtorEq] at h
    split at h <;> [rename_i hp; cases h]
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
    cases e₂ with
    | iteT _ b => obtain ⟨rfl, hq⟩ := ih h₁ ha b; exact ⟨rfl, A.meet_left hq⟩
    | iteF hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
  | iteF hc' _ ih =>
    cases hc <;> simp only [check, reduceCtorEq] at h
    split at h <;> [rename_i hp; cases h]
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
    cases e₂ with
    | iteT hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
    | iteF _ b => obtain ⟨rfl, hq⟩ := ih h₂ ha b; exact ⟨rfl, A.meet_right hq⟩
  | loopExit _ hc' ih =>
    cases hc with
    | loop σ hb =>
      simp only [check] at h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a _ => obtain ⟨rfl, hq⟩ := ih hb' hσ a; exact ⟨rfl, hq⟩
      | loopNext a hc'' _ =>
        obtain ⟨_, ha₁⟩ := ih hb' hσ a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
    | _ => simp only [check, reduceCtorEq] at h
  | @loopNext body c _ _ _ _ _ _ hc' _ ih₁ ih₂ =>
    cases hc with
    | loop σ hb =>
      simp only [check] at h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a hc'' =>
        obtain ⟨_, ha₁⟩ := ih₁ hb' hσ a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
      | loopNext a _ b =>
        obtain ⟨rfl, ha₁⟩ := ih₁ hb' hσ a
        have hloop : A.check τ' (.loop body c) (.loop σ hb) = some τ' := by
          simp only [check, hl.1, hl.2, hb', Option.bind_some, Bool.and_self, ite_true]
        obtain ⟨rfl, ha₂⟩ := ih₂ hloop ha₁ b
        exact ⟨rfl, ha₂⟩
    | _ => simp only [check, reduceCtorEq] at h
  | call hc₁ _ hr ih =>
    cases hc with
    | call hb =>
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | call hc₂ b hr₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := A.ret_sound ha₂ h₃ hr hr₂
        exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => simp only [check, reduceCtorEq] at h
  | frame => cases hc <;> simp only [check, reduceCtorEq] at h

/-- A successful check proves constant time, for any `Pub` under which the
initial states agree on what the initial taint says is public. -/
theorem constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) {hc : Hint A.T}
    (h : (A.check τ c hc).isSome = true) : ConstantTime M Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (check_sound hc (hpub _ _ h₁ h₂ hp) e₁ e₂).1

end Taint

open Lean Meta Elab Tactic in
/-- Proves `(Taint.check A τ c ?hint).isSome = true`: computes the hint
(`Taint.hintOf`, in compiled code) and then has the kernel evaluate the check.
The domain `A.T` needs a `ToExpr` instance. -/
elab "taint_decide" : tactic => do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "taint_decide: the goal is not `(Taint.check A τ c h).isSome = true`"
  let chk := lhs.appArg!
  unless chk.isAppOfArity ``Taint.check 5 do
    throwError "taint_decide: the goal is not `(Taint.check A τ c h).isSome = true`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let hty := mkApp (mkConst ``Taint.Hint) (← whnfD (mkApp2 (mkConst ``Taint.T) m a))
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) hty)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) hty inst (mkApp4 (mkConst ``Taint.hintOf) m a τ c))
  if h.isMVar then h.mvarId!.assign hv
  evalTactic (← `(tactic| decide +kernel))

end VG
