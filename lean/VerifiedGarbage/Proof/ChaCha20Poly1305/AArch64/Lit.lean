import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit

/-!
# ChaCha20-Poly1305 on AArch64: the code as literals

The code of the functions below as literals (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks each literal once here, and
then evaluates it, rather than building the instructions again, in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction), including those of its callers.
-/

namespace VG

materialize_code Impl.ChaCha20Poly1305.AArch64.seal
materialize_code Impl.ChaCha20Poly1305.AArch64.open

end VG
