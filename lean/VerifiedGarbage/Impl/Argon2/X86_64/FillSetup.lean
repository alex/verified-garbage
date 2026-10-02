import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Convert initialization's byte stride to filling dimensions and reset the public pass. -/

namespace VG.Impl.Argon2.X86_64.FillSetup

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def dimensions : List Instr :=
  [.mov .r12 (.reg .r13), .shift .shr .r12 10, .shift .shr .r13 12]

def reset : List Instr :=
  [.mov .rax (.imm 0), .store (at_ .rbp 0) .rax, .mov .rbx (.imm 0), .mov .r14 (.imm 0)]

def code : Prog isa := .seq (.block dimensions) (.block reset)

end VG.Impl.Argon2.X86_64.FillSetup
