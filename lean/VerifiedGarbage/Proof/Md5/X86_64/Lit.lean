import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Md5.X86_64

/-!
# MD5 on x86-64: the compression function as a literal
-/

namespace VG

materialize_code Impl.Md5.X86_64.compress

end VG
