import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.AArch64

materialize_code compress := Impl.Argon2.AArch64.compress

end VG.Proof.Argon2.AArch64
