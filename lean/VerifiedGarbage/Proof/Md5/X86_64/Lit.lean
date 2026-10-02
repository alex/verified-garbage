import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Md5.X86_64.Stream

/-!
# MD5 on x86-64: the code as literals
-/

namespace VG

materialize_code Impl.Md5.X86_64.compress
materialize_code Impl.Md5.X86_64.Stream.update
materialize_code Impl.Md5.X86_64.Stream.finalize

end VG
