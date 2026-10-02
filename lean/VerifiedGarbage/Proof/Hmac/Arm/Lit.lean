import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Hmac.Arm
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# HMAC-SHA-256 on Arm: the code as literals

The code of the functions below as literals (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks each literal once here, and
then evaluates it, rather than building the instructions again, in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction), including those of its callers.
-/

namespace VG

materialize_code Impl.Hmac.Arm.init
materialize_code Impl.Hmac.Arm.finalize

end VG
