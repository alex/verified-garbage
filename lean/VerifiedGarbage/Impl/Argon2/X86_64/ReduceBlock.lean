import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite

/-! XOR a last-lane block at `rsi` into the accumulator at `rdi`. -/

namespace VG.Impl.Argon2.X86_64.ReduceBlock

open VG.X86_64

def code : Prog isa := .block (FillWrite.words true 128)

end VG.Impl.Argon2.X86_64.ReduceBlock
