import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Checked literals for the public dimension setup blocks -/

namespace VG

materialize_code Impl.Argon2.X86_64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.X86_64.MemoryInit.lanesSetupCode

end VG
