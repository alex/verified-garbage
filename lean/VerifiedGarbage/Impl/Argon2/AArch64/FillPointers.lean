import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Impl.Argon2.AArch64.FillColumn

/-! Prepare the block pointers for one filling operation. `x4` is the matrix
base; `x24`, `x20`–`x23` retain the loop position. Reference mapping supplied
the reference lane and column in `x5` and `x0`. The current pointer is saved
in `x6`, with the previous and reference pointers in `x0` and `x1`.
-/

namespace VG.Impl.Argon2.AArch64.FillPointers

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def saveReference : List Instr := [mov .x1 .x0].flatten

def currentArgs : List Instr := [mov .x8 .x24].flatten

def previousArgs : List Instr := [mov .x6 .x8, mov .x3 .x0, mov .x8 .x24].flatten

def referenceArgs : List Instr := [mov .x7 .x8, mov .x3 .x1, mov .x8 .x5].flatten

def finishArgs : List Instr := [mov .x1 .x8, mov .x0 .x7].flatten

def current : Prog isa := .seq (.block currentArgs) BlockAddress.code

def previous : Prog isa := .seq (.block previousArgs) BlockAddress.code

def reference : Prog isa := .seq (.block referenceArgs) BlockAddress.code

def code : Prog isa := .seq (.block saveReference) (.seq FillColumn.code
  (.seq current (.seq previous (.seq reference (.block finishArgs)))))

end VG.Impl.Argon2.AArch64.FillPointers
