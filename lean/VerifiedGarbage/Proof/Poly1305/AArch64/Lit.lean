import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Poly1305.AArch64

/-!
# Poly1305 on AArch64: the code as literals
-/

namespace VG

materialize_code Impl.Poly1305.AArch64.init
materialize_code Impl.Poly1305.AArch64.blocks
materialize_code Impl.Poly1305.AArch64.update
materialize_code Impl.Poly1305.AArch64.finalize

end VG
