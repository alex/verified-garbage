import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Impl.Argon2.X86_64.FillLanes

/-! Visit each public lane once to reduce its last block. -/

namespace VG.Impl.Argon2.X86_64.ReduceLanes

open VG.X86_64

def advance : List Instr := FillLanes.advance

def body : Prog isa := .seq ReduceLane.code (.block advance)

def loop : Prog isa := .loop body .b

end VG.Impl.Argon2.X86_64.ReduceLanes
