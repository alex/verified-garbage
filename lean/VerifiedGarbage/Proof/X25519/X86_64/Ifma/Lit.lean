import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Ifma

/-!
# X25519 on x86-64 with AVX512_IFMA: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

namespace VG

materialize_code Impl.X25519.X86_64.x25519Ifma

end VG
