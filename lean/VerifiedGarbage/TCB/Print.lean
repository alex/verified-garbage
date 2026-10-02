import VerifiedGarbage.TCB.Code

/-!
# Lowering structured code to assembly text

**Trusted.** Structured control flow is lowered to local labels and
conditional branches:

* `ite c t e`  ⟶  `b<c> Lthen; e; b Lend; Lthen: t; Lend:`
* `loop body c` ⟶  `align; Ltop: body; b<c> Ltop`, where `align` is the
  printer's `loopAlign` (empty unless the target sets it)
* `call name body` ⟶  `<call> name` (the call instruction, e.g. `call` or
  `bl`, of the function `name`, which is emitted separately: see
  `VG.Rust.files`)
* `frame push body pop` ⟶  `push; body; pop`

Labels are numeric local labels (`N:`, referenced as `Nf` forward or `Nb`
backward), the only kind Rust allows in inline assembly (the
`named_asm_labels` lint). Every label of a function has a distinct number, so
each reference has exactly one target. The numbers are `20`, `21`, `22`, …
(`2` followed by a counter): a number of only `0`s and `1`s could be read as a
binary literal in Intel syntax.

`loopAlign` is an assembler alignment directive (e.g. `.p2align 6`), so that
where a loop's code lies relative to the processor's fetch blocks and
decoded-instruction cache lines depends on the loop alone, not on the size of
the code before it. In a code section the assembler fills the gap with NOP
instructions. They run only when execution enters the loop from the code
before it: the branch back to the top lands on the label, after them. A NOP
has no effect but advancing the instruction pointer (Intel SDM Vol. 2B,
"NOP—No Operation": it "takes up space in the instruction stream but does not
impact machine context, except for the EIP register"; flags affected: none).
So the printed code computes what the model describes, with the same memory
accesses and the same branches, taken under the same conditions: the NOPs run
on every entry into the loop whatever the data, so the leakage the model sees
is unchanged.

Together with each ISA's instruction printer this is part of the trusted
base; it is small enough to check by inspection and is covered by the golden
tests in `VerifiedGarbageTest/Print.lean`.
-/

namespace VG

/-- A line of assembly: text, or a call instruction of the function it names. -/
inductive Line
  | text (s : String)
  | call (name : String)
  deriving DecidableEq, Repr

structure Printer (M : ISA) where
  /-- Assembly text for one instruction (may be several lines). -/
  instr : M.Instr → List String
  /-- Conditional branch to a label, taken when the condition is true. -/
  branch : M.Cond → String → String
  /-- Unconditional branch to a label. -/
  jump : String → String
  /-- Return to the caller. -/
  ret : List String
  /-- The mnemonic of the call instruction whose operand is a function's
  symbol (`ISA.call`), e.g. `call` or `bl`. -/
  call : String
  /-- Assembler directives before, and after, the body of a function that
  needs the CPU feature `f` (`Artifact.features`), for an assembler that
  rejects the instructions of a feature the target does not enable: they
  enable it for that function only. -/
  enableFeature : String → List String := fun _ => []
  disableFeature : String → List String := fun _ => []
  /-- Why the assembler cannot encode an instruction as the model describes
  it (e.g. an x86-64 displacement too wide for its field, which some
  assemblers silently truncate), or `none` if it can. The emitter refuses
  code containing such an instruction (`Rust.checkEncodable`). -/
  unencodable : M.Instr → Option String := fun _ => none
  /-- Assembler directives before the top of each loop, aligning it (see the
  module docs): they may only pad with instructions that do nothing. -/
  loopAlign : List String := []

variable {M : ISA} (P : Printer M)

/-- The number of the `n`-th label of a function. -/
def labelNum (n : Nat) : String := s!"2{n}"

/-- Lower code to lines of assembly, using labels `labelNum n`; returns the
next unused label number. -/
def Printer.lower : Code M.Instr M.Cond → Nat → List Line × Nat
  | .block is, n => ((is.map P.instr).flatten.map .text, n)
  | .seq c₁ c₂, n =>
    let (l₁, n) := lower c₁ n
    let (l₂, n) := lower c₂ n
    (l₁ ++ l₂, n)
  | .ite c t e, n =>
    let lThen := labelNum n
    let lEnd := labelNum (n + 1)
    let (le, n) := lower e (n + 2)
    let (lt, n) := lower t n
    ([.text (P.branch c (lThen ++ "f"))] ++ le ++ [.text (P.jump (lEnd ++ "f")), .text (lThen ++ ":")] ++
      lt ++ [.text (lEnd ++ ":")], n)
  | .loop body c, n =>
    let lTop := labelNum n
    let (lb, n) := lower body (n + 1)
    (P.loopAlign.map .text ++ [.text (lTop ++ ":")] ++ lb ++ [.text (P.branch c (lTop ++ "b"))], n)
  | .call name _, n => ([.call name], n)
  | .frame i body j, n =>
    let (lb, n) := lower body n
    ((P.instr i).map .text ++ lb ++ (P.instr j).map .text, n)

/-- The complete body of a function: the lowered code followed by the return. -/
def Printer.function (body : Code M.Instr M.Cond) : List Line :=
  (P.lower body 0).1 ++ P.ret.map .text

end VG
