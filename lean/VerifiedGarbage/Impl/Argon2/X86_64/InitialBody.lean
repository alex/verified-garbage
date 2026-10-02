import VerifiedGarbage.Impl.Argon2.X86_64.Initial
import VerifiedGarbage.Impl.Argon2.X86_64.InitFill

/-! Complete derivation inside its enclosing argument and register-save frame. -/

namespace VG.Impl.Argon2.X86_64.InitialBody

open VG VG.X86_64

def code (name : String) (hash : HPrime.Hash) : Prog isa :=
  .seq (Initial.code hash) (InitFill.code name hash)

end VG.Impl.Argon2.X86_64.InitialBody
