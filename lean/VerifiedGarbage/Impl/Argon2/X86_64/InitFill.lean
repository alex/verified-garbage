import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Impl.Argon2.X86_64.FillSetup
import VerifiedGarbage.Impl.Argon2.X86_64.FillFinish

/-! All memory initialization, filling and finalization after H₀ has been computed. -/

namespace VG.Impl.Argon2.X86_64.InitFill

open VG.X86_64

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq (MemoryInit.code name h) (.seq FillSetup.code (FillFinish.code name h))

end VG.Impl.Argon2.X86_64.InitFill
