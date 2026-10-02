import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! # Argon2's squared mapping into an eligible reference window

`x0` contains J₁ in its low half and `x1` contains the positive window
length. Both products fit in 64 bits for the RFC's 32-bit dimensions. The
code has no branches or memory accesses, including for secret J₁ values.
-/

namespace VG.Impl.Argon2.AArch64.Relative

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .block [mov32 .x8 .x0, mul .x8, shr .x8 32, mul .x1, shr .x8 32, mov .x3 .x1, subi .x3 1, sub .x3 .x8, mov .x8 .x3].flatten

end VG.Impl.Argon2.AArch64.Relative
