import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Select block zero and the last block of the current public lane. -/

namespace VG.Impl.Argon2.X86_64.ReducePointers

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def setup : List Instr :=
  [.mov .r8 (.mem (at_ .rbp 232)), .mov .rax (.reg .rbx),
    .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)]

def finish : List Instr := [.mov .rsi (.reg .rax), .mov .rdi (.reg .r8)]

def code : Prog isa := .seq (.block setup) (.seq BlockAddress.code (.block finish))

end VG.Impl.Argon2.X86_64.ReducePointers
