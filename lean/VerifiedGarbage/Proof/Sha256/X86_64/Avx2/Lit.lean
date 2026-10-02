import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Sha256.X86_64.Avx2

/-!
# SHA-256 with AVX2 on x86-64: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.Sha256.X86_64.Avx2.compress

end VG
