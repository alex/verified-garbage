import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Poly1305.X86.Lit

/-!
# ChaCha20-Poly1305 on X86: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20Poly1305.X86.seal
materialize_code Impl.ChaCha20Poly1305.X86.open

end VG
