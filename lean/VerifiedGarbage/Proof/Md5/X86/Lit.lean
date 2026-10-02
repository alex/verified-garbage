import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Md5.X86.Stream

/-!
# MD5 on x86 (32-bit): the code as literals
-/

namespace VG

materialize_code Impl.Md5.X86.compress
materialize_code Impl.Md5.X86.Stream.update
materialize_code Impl.Md5.X86.Stream.finalize

end VG
