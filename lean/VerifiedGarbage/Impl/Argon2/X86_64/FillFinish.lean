import VerifiedGarbage.Impl.Argon2.X86_64.FillIterations
import VerifiedGarbage.Impl.Argon2.X86_64.Finish

/-! Complete all filling passes, reduce the lane endings, and compute the final tag. -/

namespace VG.Impl.Argon2.X86_64.FillFinish

open VG.X86_64

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq FillIterations.loop (Finish.code name h)

end VG.Impl.Argon2.X86_64.FillFinish
