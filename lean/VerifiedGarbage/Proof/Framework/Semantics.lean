import Mathlib.Tactic
import VerifiedGarbage.TCB.Artifact

/-!
# Reasoning about `Exec`: determinism, weakest preconditions, constant time

Untrusted: everything here is checked by Lean.
-/

namespace VG

variable {M : ISA}

theorem execBlock_append (l₁ l₂ : List M.Instr) (s : M.State) :
    execBlock M (l₁ ++ l₂) s =
      (execBlock M l₁ s).bind fun p =>
        (execBlock M l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    cases M.exec i s with
    | none => rfl
    | some s₁ =>
      simp only [ih]
      cases execBlock M is s₁ with
      | none => rfl
      | some p => simp [Option.map_map, Function.comp_def]

/-- The semantics is deterministic. -/
theorem Exec.det {c : Prog M} {s s₁ s₂ : M.State} {t₁ t₂ : List Leak}
    (h₁ : Exec M c s t₁ s₁) (h₂ : Exec M c s t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing t₂ s₂ with
  | block h => cases h₂ with
    | block h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ => cases h₂ with
    | seq a b =>
      obtain ⟨rfl, rfl⟩ := ih₁ a
      obtain ⟨rfl, rfl⟩ := ih₂ b
      exact ⟨rfl, rfl⟩
  | iteT hc _ ih => cases h₂ with
    | iteT _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
    | iteF hc' _ => rw [hc] at hc'; cases hc'
  | iteF hc _ ih => cases h₂ with
    | iteT hc' _ => rw [hc] at hc'; cases hc'
    | iteF _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
  | loopExit _ hc ih => cases h₂ with
    | loopExit a _ => obtain ⟨rfl, rfl⟩ := ih a; exact ⟨rfl, rfl⟩
    | loopNext a hc' _ =>
      obtain ⟨rfl, rfl⟩ := ih a; rw [hc] at hc'; cases hc'
  | loopNext _ hc _ ih₁ ih₂ => cases h₂ with
    | loopExit a hc' => obtain ⟨rfl, rfl⟩ := ih₁ a; rw [hc] at hc'; cases hc'
    | loopNext a _ b =>
      obtain ⟨rfl, rfl⟩ := ih₁ a
      obtain ⟨rfl, rfl⟩ := ih₂ b
      exact ⟨rfl, rfl⟩

theorem Exec.block_iff {is : List M.Instr} {s s' : M.State} {t : List Leak} :
    Exec M (.block is) s t s' ↔ execBlock M is s = some (s', t) :=
  ⟨fun h => by cases h with | block h => exact h, .block⟩

/-! ## Total-correctness weakest preconditions -/

/-- `WP M c s Q`: from `s`, `c` terminates without faulting in a state satisfying `Q`. -/
def WP (M : ISA) (c : Prog M) (s : M.State) (Q : M.State → Prop) : Prop :=
  ∃ t s', Exec M c s t s' ∧ Q s'

namespace WP

theorem mono {c : Prog M} {s : M.State} {Q Q' : M.State → Prop}
    (h : WP M c s Q) (hq : ∀ s, Q s → Q' s) : WP M c s Q' := by
  obtain ⟨t, s', he, hq'⟩ := h; exact ⟨t, s', he, hq _ hq'⟩

theorem block {is : List M.Instr} {s : M.State} {Q : M.State → Prop}
    (h : ∃ p, execBlock M is s = some p ∧ Q p.1) : WP M (.block is) s Q := by
  obtain ⟨⟨s', t⟩, h1, h2⟩ := h; exact ⟨t, s', .block h1, h2⟩

theorem block_append {l₁ l₂ : List M.Instr} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.block l₁) s (fun s₁ => WP M (.block l₂) s₁ Q)) :
    WP M (.block (l₁ ++ l₂)) s Q := by
  obtain ⟨t, s₁, h1, t', s₂, h2, hq⟩ := h
  rw [Exec.block_iff] at h1 h2
  exact ⟨t ++ t', s₂, .block (by rw [execBlock_append, h1]; simp [h2]), hq⟩

theorem block_nil {s : M.State} {Q : M.State → Prop} (h : Q s) : WP M (.block []) s Q :=
  ⟨[], s, .block rfl, h⟩

theorem seq {c₁ c₂ : Prog M} {s : M.State} {Q : M.State → Prop}
    (h : WP M c₁ s (fun s₁ => WP M c₂ s₁ Q)) : WP M (.seq c₁ c₂) s Q := by
  obtain ⟨t, s₁, h1, t', s₂, h2, hq⟩ := h; exact ⟨_, _, .seq h1 h2, hq⟩

theorem ite {c : M.Cond} {th el : Prog M} {s : M.State} {Q : M.State → Prop} (b : Bool)
    (hc : M.eval c s = some b) (ht : b = true → WP M th s Q) (he : b = false → WP M el s Q) :
    WP M (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', h1, h2⟩ := he rfl; exact ⟨_, _, .iteF hc h1, h2⟩
  · obtain ⟨t, s', h1, h2⟩ := ht rfl; exact ⟨_, _, .iteT hc h1, h2⟩

/-- The loop rule: an invariant indexed by a natural-number measure that
decreases on every iteration that loops back. -/
theorem loop {body : Prog M} {c : M.Cond} {Q : M.State → Prop}
    (Inv : Nat → M.State → Prop)
    (hstep : ∀ n s, Inv n s → WP M body s (fun s' =>
        (M.eval c s' = some false ∧ Q s') ∨
        (M.eval c s' = some true ∧ ∃ m < n, Inv m s')))
    (n : Nat) (s : M.State) (hs : Inv n s) : WP M (.loop body c) s Q := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    obtain ⟨t, s', h1, h2⟩ := hstep n s hs
    rcases h2 with ⟨hc, hq⟩ | ⟨hc, m, hm, hi⟩
    · exact ⟨_, _, .loopExit h1 hc, hq⟩
    · obtain ⟨t', s'', h3, hq⟩ := ih m hm s' hi
      exact ⟨_, _, .loopNext h1 hc h3, hq⟩

end WP

/-! ## Constant time -/

/-- Constant time follows from a *leakage function*: if every run from a
`Pre`-state `s` leaks exactly `f s`, and `f` only depends on public data. -/
theorem ConstantTime.of_leakage {Pre : M.State → Prop} {Pub : M.State → M.State → Prop}
    {c : Prog M} (f : M.State → List Leak)
    (hf : ∀ s t s', Pre s → Exec M c s t s' → t = f s)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → f s₁ = f s₂) :
    ConstantTime M Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  rw [hf _ _ _ h₁ e₁, hf _ _ _ h₂ e₂, hpub _ _ h₁ h₂ hp]

/-- A program that never leaks anything is constant time for any `Pub`. -/
theorem ConstantTime.of_silent {Pre : M.State → Prop} {Pub : M.State → M.State → Prop}
    {c : Prog M} (h : ∀ s t s', Pre s → Exec M c s t s' → t = []) :
    ConstantTime M Pre Pub c :=
  .of_leakage (fun _ => []) h (fun _ _ _ _ _ => rfl)

end VG
