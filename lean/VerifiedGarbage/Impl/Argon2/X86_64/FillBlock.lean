import VerifiedGarbage.Impl.Argon2.X86_64.RandomSource
import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel

/-! Select the random word and update one active matrix cell. -/

namespace VG.Impl.Argon2.X86_64.FillBlock

open VG.X86_64

def code : Prog isa := .seq RandomSource.code FillKernel.code

end VG.Impl.Argon2.X86_64.FillBlock
