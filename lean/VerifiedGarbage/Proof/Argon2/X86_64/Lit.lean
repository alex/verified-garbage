import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.X86_64

materialize_code compress := Impl.Argon2.X86_64.compress

end VG.Proof.Argon2.X86_64
