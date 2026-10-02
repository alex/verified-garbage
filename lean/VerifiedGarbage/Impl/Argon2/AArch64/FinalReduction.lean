import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLanes

/-! Reduce all lane endings into matrix block zero for the final H′ call. -/

namespace VG.Impl.Argon2.AArch64.FinalReduction

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code : Prog isa := .seq ReductionInit.code ReduceLanes.loop

end VG.Impl.Argon2.AArch64.FinalReduction
