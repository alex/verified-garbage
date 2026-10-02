import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.X25519.Arm

/-!
# X25519 on 32-bit ARM: the code as a literal

The code of `vg_x25519` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.X25519.Arm.x25519

end VG
