import VerifiedGarbage.TCB.Code

/-!
# Lowering structured code to assembly text

**Trusted.** Structured control flow is lowered to local labels and
conditional branches:

* `ite c t e`  ⟶  `b<c> Lthen; e; b Lend; Lthen: t; Lend:`
* `loop body c` ⟶  `Ltop: body; b<c> Ltop`

Labels are numeric local labels (`N:`, referenced as `Nf` forward or `Nb`
backward), the only kind Rust allows in inline assembly (the
`named_asm_labels` lint). Every label of a function has a distinct number, so
each reference has exactly one target. The numbers are `20`, `21`, `22`, …
(`2` followed by a counter): a number of only `0`s and `1`s could be read as a
binary literal in Intel syntax.

Together with each ISA's instruction printer this is part of the trusted
base; it is small enough to check by inspection and is covered by the golden
tests in `Proof/Framework/PrintTest.lean`.
-/

namespace VG

structure Printer (M : ISA) where
  /-- Assembly text for one instruction (may be several lines). -/
  instr : M.Instr → List String
  /-- Conditional branch to a label, taken when the condition is true. -/
  branch : M.Cond → String → String
  /-- Unconditional branch to a label. -/
  jump : String → String
  /-- Return to the caller. -/
  ret : List String

variable {M : ISA} (P : Printer M)

/-- The number of the `n`-th label of a function. -/
def labelNum (n : Nat) : String := s!"2{n}"

/-- Lower code to lines of assembly, using labels `labelNum n`; returns the
next unused label number. -/
def Printer.lower : Code M.Instr M.Cond → Nat → List String × Nat
  | .block is, n => ((is.map P.instr).flatten, n)
  | .seq c₁ c₂, n =>
    let (l₁, n) := lower c₁ n
    let (l₂, n) := lower c₂ n
    (l₁ ++ l₂, n)
  | .ite c t e, n =>
    let lThen := labelNum n
    let lEnd := labelNum (n + 1)
    let (le, n) := lower e (n + 2)
    let (lt, n) := lower t n
    ([P.branch c (lThen ++ "f")] ++ le ++ [P.jump (lEnd ++ "f"), lThen ++ ":"] ++ lt ++
      [lEnd ++ ":"], n)
  | .loop body c, n =>
    let lTop := labelNum n
    let (lb, n) := lower body (n + 1)
    ([lTop ++ ":"] ++ lb ++ [P.branch c (lTop ++ "b")], n)

/-- The complete body of a function: the lowered code followed by the return. -/
def Printer.function (body : Code M.Instr M.Cond) : List String :=
  (P.lower body 0).1 ++ P.ret

end VG
