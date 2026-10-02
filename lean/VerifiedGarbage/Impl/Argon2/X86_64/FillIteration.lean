import VerifiedGarbage.Impl.Argon2.X86_64.FillSlices

/-! Reset the slice coordinate before each filling pass. -/

namespace VG.Impl.Argon2.X86_64.FillIteration

open VG.X86_64

def setup : List Instr := [.mov .r14 (.imm 0)]

def code : Prog isa := .seq (.block setup) FillSlices.loop

end VG.Impl.Argon2.X86_64.FillIteration
