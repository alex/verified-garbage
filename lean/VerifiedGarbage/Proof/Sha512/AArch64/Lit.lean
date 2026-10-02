import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Sha512.AArch64

/-!
# SHA-512 on AArch64: the code as literals
-/

namespace VG

materialize_code Impl.Sha512.AArch64.compress

end VG
