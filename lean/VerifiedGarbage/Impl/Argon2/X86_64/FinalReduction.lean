import VerifiedGarbage.Impl.Argon2.X86_64.ReductionInit
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLanes

/-! Reduce all lane endings into matrix block zero for the final H′ call. -/

namespace VG.Impl.Argon2.X86_64.FinalReduction

open VG.X86_64

def code : Prog isa := .seq ReductionInit.code ReduceLanes.loop

end VG.Impl.Argon2.X86_64.FinalReduction
