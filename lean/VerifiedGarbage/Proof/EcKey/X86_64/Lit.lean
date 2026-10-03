import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.EcKey.P256.X86_64

/-!
# P-256 public keys on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

namespace VG

materialize_code Impl.EcKey.X86_64.publicKeyP256

end VG
