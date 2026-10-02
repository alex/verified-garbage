import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Initial
import VerifiedGarbage.Impl.Argon2.AArch64.InitFill

/-! Complete derivation inside its enclosing argument and register-save frame. -/

namespace VG.Impl.Argon2.AArch64.InitialBody

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def code (name : String) (hash : HPrime.Hash) : Prog isa :=
  .seq (Initial.code hash) (InitFill.code name hash)

end VG.Impl.Argon2.AArch64.InitialBody
