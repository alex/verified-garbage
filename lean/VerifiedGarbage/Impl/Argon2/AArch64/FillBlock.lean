import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.RandomSource
import VerifiedGarbage.Impl.Argon2.AArch64.FillKernel

/-! Select the random word and update one active matrix cell. -/

namespace VG.Impl.Argon2.AArch64.FillBlock

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .seq RandomSource.code FillKernel.code

end VG.Impl.Argon2.AArch64.FillBlock
