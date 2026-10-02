import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Divide
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Compute the rounded lane length from the normalized memory cost and lane count. -/

namespace VG.Impl.Argon2.AArch64.Parameters

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def args : List Instr :=
  [load .x0 .x19 176, load .x1 .x19 184, add .x1 .x1, add .x1 .x1].flatten

def finish : List Instr := [mov .x21 .x5, add .x21 .x21, add .x21 .x21].flatten

def code : Prog isa := .seq (.block args) (.seq Divide.code (.block finish))

end VG.Impl.Argon2.AArch64.Parameters
