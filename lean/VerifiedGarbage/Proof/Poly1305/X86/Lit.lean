import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Poly1305.X86

/-!
# Poly1305 on X86: the code as literals
-/

namespace VG

materialize_code Impl.Poly1305.X86.init
materialize_code Impl.Poly1305.X86.blocks
materialize_code Impl.Poly1305.X86.update
materialize_code Impl.Poly1305.X86.finalize

end VG
