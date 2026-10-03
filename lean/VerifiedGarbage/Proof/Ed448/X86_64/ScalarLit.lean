import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed448.X86_64.Scalar

/-!
# Ed448 scalar arithmetic on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86_64.scalarReduce
materialize_code Impl.Ed448.X86_64.scalarMulAdd

end VG
