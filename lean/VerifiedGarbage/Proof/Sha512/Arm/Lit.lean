import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sha512.Arm.Stream

/-!
# SHA-512 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Sha512.Arm.compress
materialize_code Impl.Sha512.Arm.Stream.update
materialize_code Impl.Sha512.Arm.Stream.finalize

end VG
