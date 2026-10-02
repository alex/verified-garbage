import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Sha1.AArch64.Stream

/-!
# SHA-1 on AArch64: the code as literals
-/

namespace VG

materialize_code Impl.Sha1.AArch64.compress
materialize_code Impl.Sha1.AArch64.Stream.update
materialize_code Impl.Sha1.AArch64.Stream.finalize

end VG
