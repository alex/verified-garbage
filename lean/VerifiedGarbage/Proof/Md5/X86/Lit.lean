import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Md5.X86.Stream

/-!
# MD5 on x86 (32-bit): the code as literals

Untrusted: everything here is checked by Lean. The code of the functions
below as literals (`materialize_code`, `Proof/Framework/Lit.lean`): the
kernel checks each literal once here, and then evaluates it, rather than
building the instructions again, in every check that evaluates the code
(constant time, `spSafe`, properties of every instruction), including those
of its callers.
-/

namespace VG

materialize_code Impl.Md5.X86.compress
materialize_code Impl.Md5.X86.Stream.update
materialize_code Impl.Md5.X86.Stream.finalize

end VG
