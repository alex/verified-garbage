import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Impl.Argon2.AArch64.FillSetup
import VerifiedGarbage.Impl.Argon2.AArch64.FillFinish

/-! All memory initialization, filling and finalization after H₀ has been computed. -/

namespace VG.Impl.Argon2.AArch64.InitFill

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq (MemoryInit.code name h) (.seq FillSetup.code (FillFinish.code name h))

end VG.Impl.Argon2.AArch64.InitFill
