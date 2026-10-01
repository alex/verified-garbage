import VerifiedGarbage.TCB.X86_64.Isa

/-! Start of the chronological reference window.

The public pass, slice and segment length are in `r9`, `r14` and `r13`.
`r10` receives zero on pass zero or the last slice, otherwise the column
at the beginning of the next slice. No division is needed.
-/

namespace VG.Impl.Argon2.X86_64.ReferenceStart

open VG.X86_64

def zero : List Instr := [.mov .r10 (.imm 0)]

def advance : List Instr := [
  .mov .rax (.reg .r14), .alu .add .rax (.imm 1), .mul .r13,
  .mov .r10 (.reg .rax), .alu .cmp .r14 (.imm 3)]

def code : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 0)])
    (.ite .e (.block zero)
      (.seq (.block advance) (.ite .e (.block zero) (.block []))))

end VG.Impl.Argon2.X86_64.ReferenceStart
