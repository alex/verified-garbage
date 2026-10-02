import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillSlices

/-! Reset the slice coordinate before each filling pass. -/

namespace VG.Impl.Argon2.AArch64.FillIteration

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def setup : List Instr := [imm .x22 0].flatten

def code : Prog isa := .seq (.block setup) FillSlices.loop

end VG.Impl.Argon2.AArch64.FillIteration
