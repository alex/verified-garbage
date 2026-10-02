import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Hmac.Arm
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# HMAC-SHA-256 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Hmac.Arm.init
materialize_code Impl.Hmac.Arm.finalize

end VG
