import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sha1.Arm.Stream

/-!
# SHA-1 on ARMv7: the code as literals
-/

namespace VG

materialize_code Impl.Sha1.Arm.compress
materialize_code Impl.Sha1.Arm.Stream.update
materialize_code Impl.Sha1.Arm.Stream.finalize

end VG
