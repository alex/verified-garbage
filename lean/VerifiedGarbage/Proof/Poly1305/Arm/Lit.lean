import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Poly1305.Arm

/-!
# Poly1305 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Poly1305.Arm.init
materialize_code Impl.Poly1305.Arm.blocks
materialize_code Impl.Poly1305.Arm.update
materialize_code Impl.Poly1305.Arm.finalize

end VG
