import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.ReducePointers
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock

/-! Accumulate one lane's last block into matrix block zero. -/

namespace VG.Impl.Argon2.AArch64.ReduceLane

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .seq ReducePointers.code ReduceBlock.code

end VG.Impl.Argon2.AArch64.ReduceLane
