import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Impl.Argon2.X86_64.FillColumn

/-! Prepare the block pointers for one filling operation. `r8` is the matrix
base; `rbx`, `r12`–`r15` retain the loop position. Reference mapping supplied
the reference lane and column in `r9` and `rdi`. The current pointer is saved
in `r10`, with the previous and reference pointers in `rdi` and `rsi`.
-/

namespace VG.Impl.Argon2.X86_64.FillPointers

open VG.X86_64

def saveReference : List Instr := [.mov .rsi (.reg .rdi)]

def currentArgs : List Instr := [.mov .rax (.reg .rbx)]

def previousArgs : List Instr := [
  .mov .r10 (.reg .rax), .mov .rcx (.reg .rdi), .mov .rax (.reg .rbx)]

def referenceArgs : List Instr := [
  .mov .r11 (.reg .rax), .mov .rcx (.reg .rsi), .mov .rax (.reg .r9)]

def finishArgs : List Instr := [.mov .rsi (.reg .rax), .mov .rdi (.reg .r11)]

def current : Prog isa := .seq (.block currentArgs) BlockAddress.code

def previous : Prog isa := .seq (.block previousArgs) BlockAddress.code

def reference : Prog isa := .seq (.block referenceArgs) BlockAddress.code

def code : Prog isa := .seq (.block saveReference) (.seq FillColumn.code
  (.seq current (.seq previous (.seq reference (.block finishArgs)))))

end VG.Impl.Argon2.X86_64.FillPointers
