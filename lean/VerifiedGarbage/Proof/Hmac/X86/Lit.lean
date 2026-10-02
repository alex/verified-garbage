import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# HMAC-SHA-256 on X86: the code as literals
-/

namespace VG

materialize_code Impl.Hmac.X86.init
materialize_code Impl.Hmac.X86.finalizeHash
materialize_code Impl.Hmac.X86.finalize

end VG
