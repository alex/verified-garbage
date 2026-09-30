import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.X25519.Arm

/-!
# X25519 on 32-bit ARM: the code as a literal

Untrusted: everything here is checked by Lean. The code of `vg_x25519` as a
literal (`materialize_code`, `Proof/Framework/Lit.lean`): the kernel checks
the literal once here, and then evaluates it, rather than building the
instructions again, in every check that evaluates the code (constant time).
-/

namespace VG

materialize_code Impl.X25519.Arm.x25519

end VG
