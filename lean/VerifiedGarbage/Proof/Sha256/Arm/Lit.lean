import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sha256.Arm.Stream

/-!
# SHA-256 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Sha256.Arm.compress
materialize_code Impl.Sha256.Arm.Stream.update
materialize_code Impl.Sha256.Arm.Stream.finalize

end VG
