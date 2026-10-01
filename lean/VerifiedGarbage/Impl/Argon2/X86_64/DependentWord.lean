import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel

/-! Read the previous cell's first word for data-dependent addressing. Only the
public loop position and matrix base determine the read address.
-/

namespace VG.Impl.Argon2.X86_64.DependentWord

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def args : List Instr := [.mov .rcx (.reg .rdi), .mov .rax (.reg .rbx)]

def pointer : Prog isa := .seq (.block FillKernel.matrix)
  (.seq FillColumn.code (.seq (.block args) BlockAddress.code))

def read : List Instr := [.mov .rdi (.mem (at_ .rax 0))]

def code : Prog isa := .seq pointer (.block read)

end VG.Impl.Argon2.X86_64.DependentWord
