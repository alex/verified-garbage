import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.X448.Arm

/-!
# X448 on ARMv7: the code as a literal

Materializing the code once avoids rebuilding the unrolled arithmetic in each
kernel-evaluated check.
-/

namespace VG

materialize_code Impl.X448.Arm.x448

end VG
