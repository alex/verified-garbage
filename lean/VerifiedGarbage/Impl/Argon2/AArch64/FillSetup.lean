import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Convert initialization's byte stride to filling dimensions and reset the public pass. -/

namespace VG.Impl.Argon2.AArch64.FillSetup

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def dimensions : List Instr :=
  [mov .x20 .x21, shr .x20 10, shr .x21 12].flatten

def reset : List Instr :=
  [imm .x8 0, store .x19 0 .x8, imm .x24 0, imm .x22 0].flatten

def code : Prog isa := .seq (.block dimensions) (.block reset)

end VG.Impl.Argon2.AArch64.FillSetup
