import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite

/-! XOR a last-lane block at `x1` into the accumulator at `x0`. -/

namespace VG.Impl.Argon2.AArch64.ReduceBlock

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .block (FillWrite.words true 128)

end VG.Impl.Argon2.AArch64.ReduceBlock
