import VerifiedGarbage.Impl.Argon2.X86_64.FillLanes

/-! Reset the lane coordinate and fill every lane of one slice. -/

namespace VG.Impl.Argon2.X86_64.FillSlice

open VG.X86_64

def setup : List Instr := [.mov .rbx (.imm 0)]

def code : Prog isa := .seq (.block setup) FillLanes.loop

end VG.Impl.Argon2.X86_64.FillSlice
