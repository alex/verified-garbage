import VerifiedGarbage.Impl.Argon2.X86_64.ReducePointers
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceBlock

/-! Accumulate one lane's last block into matrix block zero. -/

namespace VG.Impl.Argon2.X86_64.ReduceLane

open VG.X86_64

def code : Prog isa := .seq ReducePointers.code ReduceBlock.code

end VG.Impl.Argon2.X86_64.ReduceLane
