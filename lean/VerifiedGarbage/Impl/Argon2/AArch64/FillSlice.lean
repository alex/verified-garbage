import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes

/-! Reset the lane coordinate and fill every lane of one slice. -/

namespace VG.Impl.Argon2.AArch64.FillSlice

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def setup : List Instr := [imm .x24 0].flatten

def code : Prog isa := .seq (.block setup) FillLanes.loop

end VG.Impl.Argon2.AArch64.FillSlice
