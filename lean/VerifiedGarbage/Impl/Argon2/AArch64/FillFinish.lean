import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillIterations
import VerifiedGarbage.Impl.Argon2.AArch64.Finish

/-! Complete all filling passes, reduce the lane endings, and compute the final tag. -/

namespace VG.Impl.Argon2.AArch64.FillFinish

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq FillIterations.loop (Finish.code name h)

end VG.Impl.Argon2.AArch64.FillFinish
