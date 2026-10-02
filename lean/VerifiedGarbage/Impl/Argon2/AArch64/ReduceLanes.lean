import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Impl.Argon2.AArch64.FillLanes

/-! Visit each public lane once to reduce its last block. -/

namespace VG.Impl.Argon2.AArch64.ReduceLanes

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def advance : List Instr := FillLanes.advance

def body : Prog isa := .seq ReduceLane.code (.block advance)

def loop : Prog isa := .loop body (.nonzero .x .x14)

end VG.Impl.Argon2.AArch64.ReduceLanes
