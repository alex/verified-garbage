import VerifiedGarbage.TCB.X86_64.Isa

/-! # Select the eligible window without branching on the reference lane

`rdi,rsi` are the reference and current lanes; `rdx,rcx` hold the same-lane
and cross-lane window lengths. `r8` receives the selected length. Subtracting
one from the lanes' XOR borrows exactly when the lanes match, supplying the
mask for the selection. The counts may be secret too.
-/

namespace VG.Impl.Argon2.X86_64.SelectWindow

open VG.X86_64

def code : Prog isa := .block [
  .mov .rax (.reg .rdi), .alu .xor .rax (.reg .rsi), .alu .sub .rax (.imm 1),
  .alu .sbb .rax (.reg .rax), .mov .r8 (.reg .rcx), .alu .xor .rdx (.reg .rcx),
  .alu .and .rdx (.reg .rax), .alu .xor .r8 (.reg .rdx)]

end VG.Impl.Argon2.X86_64.SelectWindow
