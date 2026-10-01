import VerifiedGarbage.TCB.X86_64.Isa

/-! # Argon2's squared mapping into an eligible reference window

`rdi` contains J₁ in its low half and `rsi` contains the positive window
length. Both products fit in 64 bits for the RFC's 32-bit dimensions. The
code has no branches or memory accesses, including for secret J₁ values.
-/

namespace VG.Impl.Argon2.X86_64.Relative

open VG.X86_64

def code : Prog isa := .block [
  .mov32 .rax (.reg .rdi), .mul .rax, .shift .shr .rax 32,
  .mul .rsi, .shift .shr .rax 32, .mov .rcx (.reg .rsi),
  .alu .sub .rcx (.imm 1), .alu .sub .rcx (.reg .rax), .mov .rax (.reg .rcx)]

end VG.Impl.Argon2.X86_64.Relative
