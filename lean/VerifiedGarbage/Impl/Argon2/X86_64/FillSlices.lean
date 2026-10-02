import VerifiedGarbage.Impl.Argon2.X86_64.FillSlice

/-! Fill a pass's four slices in order, using the public slice coordinate. -/

namespace VG.Impl.Argon2.X86_64.FillSlices

open VG.X86_64

def advance : List Instr := [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 4)]

def body : Prog isa := .seq FillSlice.code (.block advance)

def loop : Prog isa := .loop body .b

end VG.Impl.Argon2.X86_64.FillSlices
