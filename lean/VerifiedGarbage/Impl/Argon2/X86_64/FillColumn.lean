import VerifiedGarbage.TCB.X86_64.Isa

/-! Current and preceding columns in the filling loop. The public slice,
segment length and offset are in `r14`, `r13` and `r15`, and the lane length
is in `r12`. `rcx` receives the current column; `rdi` receives its cyclic
predecessor. Only the public column-zero test controls a branch.
-/

namespace VG.Impl.Argon2.X86_64.FillColumn

open VG.X86_64

def current : List Instr := [
  .mov .rax (.reg .r14), .mul .r13, .mov .rcx (.reg .rax),
  .alu .add .rcx (.reg .r15)]

def select : Prog isa := .ite .e
  (.block [.mov .rdi (.reg .r12)]) (.block [.mov .rdi (.reg .rcx)])

def previous : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.imm 0)])
    (.seq select (.block [.alu .sub .rdi (.imm 1)]))

def code : Prog isa := .seq (.block current) previous

end VG.Impl.Argon2.X86_64.FillColumn
