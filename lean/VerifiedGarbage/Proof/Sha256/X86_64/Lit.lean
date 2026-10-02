import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Sha256.X86_64

/-!
# SHA-256 on X86_64: the code as literals
-/

namespace VG

materialize_code Impl.Sha256.X86_64.compress

end VG
