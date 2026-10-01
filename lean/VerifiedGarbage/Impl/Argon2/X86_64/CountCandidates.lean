import VerifiedGarbage.TCB.X86_64.Isa

/-! # The two eligible reference windows

`r9` is the pass, `r12` the lane length, `r13` the segment length, `r14`
the slice and `r15` the index within the segment. `rdx` receives the count
for the current lane; `rcx` receives the count for another lane. Only the
public pass controls a branch. The zero-index adjustment uses a borrow mask.
-/

namespace VG.Impl.Argon2.X86_64.CountCandidates

open VG.X86_64

def first : List Instr := [
  .mov .rax (.reg .r13), .mul .r14, .mov .rcx (.reg .rax), .mov .rdx (.reg .rax),
  .alu .add .rdx (.reg .r15), .alu .sub .rdx (.imm 1)]

def later : List Instr := [
  .mov .rax (.reg .r12), .alu .sub .rax (.reg .r13), .mov .rcx (.reg .rax),
  .mov .rdx (.reg .rax), .alu .add .rdx (.reg .r15), .alu .sub .rdx (.imm 1)]

def adjust : List Instr := [
  .mov .r8 (.reg .r15), .alu .sub .r8 (.imm 1), .alu .sbb .r9 (.reg .r9),
  .alu .add .rcx (.reg .r9)]

def code : Prog isa :=
  .seq (.block [.alu .cmp .r9 (.imm 0)])
    (.seq (.ite .e (.block first) (.block later)) (.block adjust))

end VG.Impl.Argon2.X86_64.CountCandidates
