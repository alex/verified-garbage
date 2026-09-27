import VerifiedGarbage.TCB.Mem

/-!
# Structured assembly programs and their semantics

**Trusted.** Every architecture model instantiates `ISA`: a machine state, a
type of straight-line instructions with a partial semantics, and a type of
branch conditions.

Programs are `Code`: straight-line blocks of real instructions glued together
with structured control flow (`ite` and do-while `loop`). The printer
(`TCB/Print.lean`) lowers the structured control flow to labels and
conditional jumps.

## Semantics, safety and leakage

`Exec M c s t s'` means: running `c` from `s` terminates in `s'` without
faulting, producing the leakage trace `t`. An instruction faults (`exec`
returns `none`) on any memory access outside the regions the state permits,
and on reading an undefined flag; so a proof of `∃ t s', Exec M c s t s' ∧ …`
establishes termination, memory safety and functional correctness at once.

The leakage trace records every memory address accessed and every branch
decision: the standard constant-time leakage model. Instructions whose timing
depends on their operand values (e.g. division) must not be part of any ISA
model.
-/

namespace VG

/-- One observation of the constant-time attacker. -/
inductive Leak where
  | addr (a : Addr)
  | branch (taken : Bool)
  deriving DecidableEq, Repr

/-- The interface between an architecture model and the generic framework. -/
structure ISA where
  State : Type
  Instr : Type
  Cond : Type
  /-- Semantics of a straight-line instruction; `none` means the machine faults. -/
  exec : Instr → State → Option State
  /-- The addresses of the memory accessed by an instruction. -/
  addrs : Instr → State → List Addr
  /-- Evaluate a branch condition; `none` if it depends on an undefined flag. -/
  eval : Cond → State → Option Bool

/-- Structured code. -/
inductive Code (I C : Type) where
  | block (is : List I)
  | seq (c₁ c₂ : Code I C)
  /-- `if c then t else e` -/
  | ite (c : C) (t e : Code I C)
  /-- `do body while c` -/
  | loop (body : Code I C) (c : C)

variable (M : ISA)

abbrev Prog := Code M.Instr M.Cond

/-- Run a straight-line block. -/
def execBlock : List M.Instr → M.State → Option (M.State × List Leak)
  | [], s => some (s, [])
  | i :: is, s =>
    match M.exec i s with
    | none => none
    | some s₁ => (execBlock is s₁).map fun p => (p.1, (M.addrs i s).map Leak.addr ++ p.2)

/-- Big-step semantics: terminating, non-faulting executions with their leakage traces. -/
inductive Exec : Prog M → M.State → List Leak → M.State → Prop
  | block {is s s' t} : execBlock M is s = some (s', t) → Exec (.block is) s t s'
  | seq {c₁ c₂ s₁ s₂ s₃ t₁ t₂} :
      Exec c₁ s₁ t₁ s₂ → Exec c₂ s₂ t₂ s₃ → Exec (.seq c₁ c₂) s₁ (t₁ ++ t₂) s₃
  | iteT {c th el s s' t} :
      M.eval c s = some true → Exec th s t s' → Exec (.ite c th el) s (.branch true :: t) s'
  | iteF {c th el s s' t} :
      M.eval c s = some false → Exec el s t s' → Exec (.ite c th el) s (.branch false :: t) s'
  | loopExit {body c s s' t} :
      Exec body s t s' → M.eval c s' = some false →
      Exec (.loop body c) s (t ++ [.branch false]) s'
  | loopNext {body c s s' s'' t t'} :
      Exec body s t s' → M.eval c s' = some true → Exec (.loop body c) s' t' s'' →
      Exec (.loop body c) s (t ++ .branch true :: t') s''

/-- `c` is constant-time with respect to `Pub` ("the two initial states agree
on all public data") under the precondition `Pre`: any two terminating runs
from states that agree on public data produce identical leakage traces. -/
def ConstantTime (Pre : M.State → Prop) (Pub : M.State → M.State → Prop) (c : Prog M) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', Pre s₁ → Pre s₂ → Pub s₁ s₂ →
    Exec M c s₁ t₁ s₁' → Exec M c s₂ t₂ s₂' → t₁ = t₂

end VG
