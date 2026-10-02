import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor

/-!
# ChaCha20 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20.Arm.block
materialize_code Impl.ChaCha20.Arm.Xor.xor

end VG
