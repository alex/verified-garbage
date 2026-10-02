import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Poly1305.Arm

/-!
# Poly1305 on Arm: the code as literals

The code of the functions below as literals (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks each literal once here, and
then evaluates it, rather than building the instructions again, in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction), including those of its callers.
-/

namespace VG

materialize_code Impl.Poly1305.Arm.init
materialize_code Impl.Poly1305.Arm.blocks
materialize_code Impl.Poly1305.Arm.update
materialize_code Impl.Poly1305.Arm.finalize

end VG
