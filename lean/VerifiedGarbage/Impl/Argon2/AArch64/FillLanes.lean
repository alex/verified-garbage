import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.SegmentSetup

/-! Fill one slice's lanes serially, advancing only the public lane coordinate. -/

namespace VG.Impl.Argon2.AArch64.FillLanes

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def advance : List Instr := [addi .x24 1, comparem .x24 .x19 184].flatten

def body : Prog isa := .seq SegmentSetup.code (.block advance)

def loop : Prog isa := .loop body (.nonzero .x .x14)

end VG.Impl.Argon2.AArch64.FillLanes
