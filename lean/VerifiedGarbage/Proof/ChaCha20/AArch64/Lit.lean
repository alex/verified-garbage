import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor

/-!
# ChaCha20 on AArch64: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20.AArch64.block
materialize_code Impl.ChaCha20.AArch64.Xor.xor

end VG
