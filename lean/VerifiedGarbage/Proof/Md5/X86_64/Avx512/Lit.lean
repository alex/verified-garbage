import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Md5.X86_64.Avx512

/-!
# MD5 on x86-64 with AVX-512: the code as a literal
-/

namespace VG

materialize_code Impl.Md5.X86_64.Avx512.compress

end VG
