import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Checked literals for the public dimension setup blocks -/

namespace VG

materialize_code Impl.Argon2.AArch64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.AArch64.MemoryInit.lanesSetupCode

end VG
