import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Pbkdf2.Arm
import VerifiedGarbage.Proof.Hmac.Arm.Lit

/-!
# PBKDF2-HMAC-SHA-256 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Pbkdf2.Arm.iterate

end VG
