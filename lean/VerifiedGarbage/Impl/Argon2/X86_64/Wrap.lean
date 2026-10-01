import VerifiedGarbage.TCB.X86_64.Isa

/-! # Wrap a reference-column sum with one masked subtraction

`rdi` is the sum and `rsi` the positive lane length. A sum below twice the
lane length needs at most one subtraction; the borrow mask selects the
original sum when it is already in range. No secret controls a branch.
-/

namespace VG.Impl.Argon2.X86_64.Wrap

open VG.X86_64

def code : Prog isa := .block [
  .mov .r10 (.reg .rdi), .alu .sub .rdi (.reg .rsi), .alu .sbb .rax (.reg .rax),
  .alu .xor .r10 (.reg .rdi), .alu .and .r10 (.reg .rax), .alu .xor .rdi (.reg .r10)]

end VG.Impl.Argon2.X86_64.Wrap
