import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha256.X86.Stream

/-!
# SHA-256 on X86: the code as literals
-/

namespace VG

materialize_code Impl.Sha256.X86.compress
materialize_code Impl.Sha256.X86.Stream.update
materialize_code Impl.Sha256.X86.Stream.finalize

end VG
