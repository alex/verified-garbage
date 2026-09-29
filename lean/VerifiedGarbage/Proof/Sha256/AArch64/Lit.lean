import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Sha256.AArch64.Stream

/-!
# SHA-256 on AArch64: the code as literals

Untrusted: everything here is checked by Lean. The code of the functions
below as literals (`materialize_code`, `Proof/Framework/Lit.lean`): the
kernel checks each literal once here, and then evaluates it, rather than
building the instructions again, in every check that evaluates the code
(constant time, `spSafe`, properties of every instruction), including those
of its callers.
-/

namespace VG

materialize_code Impl.Sha256.AArch64.compress
materialize_code Impl.Sha256.AArch64.Stream.update
materialize_code Impl.Sha256.AArch64.Stream.finalize

end VG
