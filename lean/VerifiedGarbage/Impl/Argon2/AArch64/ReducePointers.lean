import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Select block zero and the last block of the current public lane. -/

namespace VG.Impl.Argon2.AArch64.ReducePointers

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def setup : List Instr :=
  [load .x4 .x19 232, mov .x8 .x24, mov .x3 .x20, subi .x3 1].flatten

def finish : List Instr := [mov .x1 .x8, mov .x0 .x4].flatten

def code : Prog isa := .seq (.block setup) (.seq BlockAddress.code (.block finish))

end VG.Impl.Argon2.AArch64.ReducePointers
