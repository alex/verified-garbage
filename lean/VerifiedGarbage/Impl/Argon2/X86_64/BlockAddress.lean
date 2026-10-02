import VerifiedGarbage.TCB.X86_64.Isa

/-! Lane-major matrix addressing. The matrix base is in `r8`, the lane
in `rax`, the column in `rcx`, and the lane length in `r12`. The resulting
block pointer is returned in `rax`. Scalar multiplication and ten doublings
work on the baseline ISA, including when the reference coordinates are secret.
-/

namespace VG.Impl.Argon2.X86_64.BlockAddress

open VG.X86_64

def flatten : List Instr := [.mul .r12, .alu .add .rax (.reg .rcx)]

def scale : List Instr := List.replicate 10 (.alu .add .rax (.reg .rax))

def code : Prog isa :=
  .seq (.block flatten) (.seq (.block scale) (.block [.alu .add .rax (.reg .r8)]))

end VG.Impl.Argon2.X86_64.BlockAddress
