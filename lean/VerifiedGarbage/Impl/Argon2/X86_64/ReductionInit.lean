import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Begin the final reduction at lane zero with a zero accumulator in matrix block zero. -/

namespace VG.Impl.Argon2.X86_64.ReductionInit

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def setup : List Instr := [.mov .rdi (.mem (at_ .rbp 232)), .mov .rbx (.imm 0)]

def code : Prog isa := .seq (.block setup) ClearBlock.code

end VG.Impl.Argon2.X86_64.ReductionInit
