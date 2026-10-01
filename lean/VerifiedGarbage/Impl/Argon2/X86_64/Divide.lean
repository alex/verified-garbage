import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Fixed-time unsigned division for Argon2's block indices

The numerator in `rdi` and positive divisor in `rsi` fit in 32 bits.
The result is a quotient in `r9` and remainder in `r8`. Each of the 32
input bits takes the same instruction sequence, including masked selection
of the reduced remainder. This also handles secret address words without
leaking anything through division latency or a conditional branch.
-/

namespace VG.Impl.Argon2.X86_64.Divide

open VG.X86_64

/-- Shift in input bit `j` and subtract the divisor once. -/
def subtract (j : Nat) : List Instr :=
  [.mov .rcx (.reg .rdi), .shift .shr .rcx (j + 1),
    .alu .adc .r8 (.reg .r8), .mov .r10 (.reg .r8),
    .alu .sub .r8 (.reg .rsi), .alu .sbb .rax (.reg .rax)]

/-- Restore the unreduced remainder on borrow and append the quotient bit. -/
def select : List Instr :=
  [.alu .xor .r10 (.reg .r8), .alu .and .r10 (.reg .rax),
    .alu .xor .r8 (.reg .r10), .alu .add .rax (.imm 1),
    .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .rax)]

def bit (j : Nat) : List Instr := subtract j ++ select

/-- All iterations are unrolled, independent of either operand. -/
def code : Prog isa :=
  .block ([.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0), .mov32 .rax (.imm 0), .alu .cmp .rax (.imm 0)] ++
    (List.range 32).reverse.flatMap bit)

end VG.Impl.Argon2.X86_64.Divide
