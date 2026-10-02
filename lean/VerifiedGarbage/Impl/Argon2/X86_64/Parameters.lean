import VerifiedGarbage.Impl.Argon2.X86_64.Divide
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Compute the rounded lane length from the normalized memory cost and lane count. -/

namespace VG.Impl.Argon2.X86_64.Parameters

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def args : List Instr :=
  [.mov .rdi (.mem (at_ .rbp 176)), .mov .rsi (.mem (at_ .rbp 184)),
    .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)]

def finish : List Instr := [.mov .r13 (.reg .r9), .alu .add .r13 (.reg .r13), .alu .add .r13 (.reg .r13)]

def code : Prog isa := .seq (.block args) (.seq Divide.code (.block finish))

end VG.Impl.Argon2.X86_64.Parameters
