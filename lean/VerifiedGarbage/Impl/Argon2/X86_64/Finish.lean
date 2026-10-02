import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
import VerifiedGarbage.Impl.Argon2.X86_64.FinalOutput

/-! The complete final reduction and H′, parameterized by the hash backend. -/

namespace VG.Impl.Argon2.X86_64.Finish

open VG.X86_64

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq FinalReduction.code (FinalOutput.code name h)

end VG.Impl.Argon2.X86_64.Finish
