import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2

/-!
# Poly1305 on x86-64 with AVX2: the code as a literal

Untrusted: everything here is checked by Lean. `blocksAvx2` as a literal
(`materialize_code`, `Proof/Framework/Lit.lean`), which the kernel checks
once here and then evaluates in every check of the code (constant time,
`spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.Poly1305.X86_64.Avx2.blocksAvx2

end VG
