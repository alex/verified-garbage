import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillSlice

/-! Fill a pass's four slices in order, using the public slice coordinate. -/

namespace VG.Impl.Argon2.AArch64.FillSlices

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def advance : List Instr := [addi .x22 1, comparei .x22 4].flatten

def body : Prog isa := .seq FillSlice.code (.block advance)

def loop : Prog isa := .loop body (.nonzero .x .x14)

end VG.Impl.Argon2.AArch64.FillSlices
