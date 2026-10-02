import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! Start of the chronological reference window.

The public pass, slice and segment length are in `x5`, `x22` and `x21`.
`x6` receives zero on pass zero or the last slice, otherwise the column
at the beginning of the next slice. No division is needed.
-/

namespace VG.Impl.Argon2.AArch64.ReferenceStart

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def zero : List Instr := [imm .x6 0].flatten

def advance : List Instr := [mov .x8 .x22, addi .x8 1, mul .x21, mov .x6 .x8, comparei .x22 3].flatten

def code : Prog isa :=
  .seq (.block [comparei .x5 0].flatten)
    (.ite (.zero .x .x15) (.block zero)
      (.seq (.block advance) (.ite (.zero .x .x15) (.block zero) (.block []))))

end VG.Impl.Argon2.AArch64.ReferenceStart
