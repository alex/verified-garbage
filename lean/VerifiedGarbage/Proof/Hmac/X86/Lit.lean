import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# HMAC-SHA-256 on X86: the code as literals

Untrusted: everything here is checked by Lean. The code of the functions
below as literals (`materialize_code`, `Proof/Framework/Lit.lean`): the
kernel checks each literal once here, and then evaluates it, rather than
building the instructions again, in every check that evaluates the code
(constant time, `spSafe`, properties of every instruction), including those
of its callers.
-/

namespace VG

materialize_code Impl.Hmac.X86.init
materialize_code Impl.Hmac.X86.finalize

end VG
