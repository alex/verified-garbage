import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Final H′: matrix block zero is the input, using the derivation's hash backend. -/

namespace VG.Impl.Argon2.X86_64.FinalOutput

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def args : List Instr :=
  [.mov .rdi (.mem (at_ .rbp 232)), .mov .rsi (.imm 1024),
    .mov .rdx (.mem (at_ .rbp 256)), .mov .rcx (.mem (at_ .rbp 264)),
    .mov .r8 (.mem (at_ .rbp 248))]

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq (.block args) (.call name (HPrime.code h))

end VG.Impl.Argon2.X86_64.FinalOutput
