import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillBlock

/-! Advance the public index after each active cell, stopping at the segment length. -/

namespace VG.Impl.Argon2.AArch64.FillSegment

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def advance : List Instr := [addi .x23 1, Instructions.compare .x23 .x21].flatten

def body : Prog isa := .seq FillBlock.code (.block advance)

def loop : Prog isa := .loop body (.nonzero .x .x14)

end VG.Impl.Argon2.AArch64.FillSegment
