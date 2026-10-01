import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.Divide

/-! A checked literal for the unrolled index-division code. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Divide.code

end VG
