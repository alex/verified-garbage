import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64

/-!
# Poly1305 on X86_64: the code as literals
-/

namespace VG

materialize_code Impl.Poly1305.X86_64.init
materialize_code Impl.Poly1305.X86_64.blocks
materialize_code Impl.Poly1305.X86_64.updatePre
materialize_code Impl.Poly1305.X86_64.updatePost
materialize_code Impl.Poly1305.X86_64.finalize

end VG
