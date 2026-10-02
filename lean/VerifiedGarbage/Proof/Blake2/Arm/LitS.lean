import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Blake2.Arm.CompressS

/-!
# BLAKE2s on ARMv7: the code as a literal

The code of the compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.Blake2.Arm.S.compress

end VG
