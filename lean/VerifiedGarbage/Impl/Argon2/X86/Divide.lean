import VerifiedGarbage.Impl.Argon2.X86.Layout

/-!
# Fixed-time unsigned division on x86 (32-bit)

`ecx` holds the numerator and `[ebp + d]` the positive divisor, below 2³¹.
Each of the 32 bits, from the most significant, takes the same eight
instructions: `add ecx, ecx` shifts the next numerator bit out into CF
(and makes room for a quotient bit at the bottom of `ecx`), `adc` shifts it
into the remainder in `eax`, the divisor is subtracted, and the borrow mask
in `edx` adds the divisor back and gives the quotient bit. The quotient ends
in `ecx` and the remainder in `eax`. There are no branches, and the only
memory access is the divisor's word, so the numerator may be secret.
-/

namespace VG.Impl.Argon2.X86.Divide

open VG.X86
open VG.Impl.Sha512.X86 (at_)

/-- One bit of the division by `[ebp + d]`. -/
def bit (d : Nat) : List Instr :=
  [.alu .add .ecx (.reg .ecx), .alu .adc .eax (.reg .eax), .alu .sub .eax (.mem (at_ .ebp d)),
    .alu .sbb .edx (.reg .edx), .alu .add .ecx (.imm 1), .alu .add .ecx (.reg .edx),
    .alu .and .edx (.mem (at_ .ebp d)), .alu .add .eax (.reg .edx)]

/-- `n` bits. -/
def bits (d : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => bits d n ++ bit d

def code (d : Nat) : List Instr := .mov .eax (.imm 0) :: bits d 32

end VG.Impl.Argon2.X86.Divide
