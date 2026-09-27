import VerifiedGarbage.TCB.Code

/-!
# Lowering structured code to assembly text

**Trusted.** Structured control flow is lowered to local labels and
conditional branches:

* `ite c t e`  ⟶  `b<c> Lthen; e; b Lend; Lthen: t; Lend:`
* `loop body c` ⟶  `Ltop: body; b<c> Ltop`

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

/-- Lower code to lines of assembly, using labels `.L<pfx>_<n>`; returns the
next unused label number. -/
def Printer.lower (pfx : String) : Code M.Instr M.Cond → Nat → List String × Nat
  | .block is, n => ((is.map P.instr).flatten, n)
  | .seq c₁ c₂, n =>
    let (l₁, n) := lower pfx c₁ n
    let (l₂, n) := lower pfx c₂ n
    (l₁ ++ l₂, n)
  | .ite c t e, n =>
    let lThen := s!".L{pfx}_{n}"
    let lEnd := s!".L{pfx}_{n+1}"
    let (le, n) := lower pfx e (n + 2)
    let (lt, n) := lower pfx t n
    ([P.branch c lThen] ++ le ++ [P.jump lEnd, lThen ++ ":"] ++ lt ++ [lEnd ++ ":"], n)
  | .loop body c, n =>
    let lTop := s!".L{pfx}_{n}"
    let (lb, n) := lower pfx body (n + 1)
    ([lTop ++ ":"] ++ lb ++ [P.branch c lTop], n)

/-- The complete body of a function: the lowered code followed by the return. -/
def Printer.function (pfx : String) (body : Code M.Instr M.Cond) : List String :=
  (P.lower pfx body 0).1 ++ P.ret

end VG
