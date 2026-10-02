import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.ChaCha20.X86.Xor

/-!
# ChaCha20 on X86: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20.X86.block
materialize_code Impl.ChaCha20.X86.Xor.xor

end VG
