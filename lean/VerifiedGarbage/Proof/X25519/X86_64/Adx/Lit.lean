import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Adx

/-!
# X25519 on x86-64 with BMI2 and ADX: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

namespace VG

materialize_code Impl.X25519.X86_64.x25519Adx

end VG
