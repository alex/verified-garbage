import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Blake2.Arm.CompressB

/-!
# BLAKE2b on ARMv7: the code as a literal

The code of the compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks it once here, and then
evaluates it, rather than building the instructions again, in every check that
evaluates the code (constant time, `spSafe`).
-/

namespace VG

materialize_code Impl.Blake2.Arm.B.compress

end VG
