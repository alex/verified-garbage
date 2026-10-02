import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
import VerifiedGarbage.Proof.Poly1305.Arm.Lit

/-!
# ChaCha20-Poly1305 on Arm: the code as literals
-/

namespace VG

-- The parts of the code that the constant-time proofs analyse on their own.
materialize_code Impl.ChaCha20Poly1305.Arm.sealMain
materialize_code Impl.ChaCha20Poly1305.Arm.openMain
materialize_code Impl.ChaCha20Poly1305.Arm.openEnd
materialize_code Impl.ChaCha20Poly1305.Arm.seal
materialize_code Impl.ChaCha20Poly1305.Arm.open

end VG
