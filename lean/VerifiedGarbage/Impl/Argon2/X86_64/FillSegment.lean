import VerifiedGarbage.Impl.Argon2.X86_64.FillBlock

/-! Advance the public index after each active cell, stopping at the segment length. -/

namespace VG.Impl.Argon2.X86_64.FillSegment

open VG.X86_64

def advance : List Instr := [.alu .add .r15 (.imm 1), .alu .cmp .r15 (.reg .r13)]

def body : Prog isa := .seq FillBlock.code (.block advance)

def loop : Prog isa := .loop body .b

end VG.Impl.Argon2.X86_64.FillSegment
