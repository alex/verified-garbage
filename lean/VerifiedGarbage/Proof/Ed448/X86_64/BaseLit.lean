import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase

/-!
# Ed448 base-point multiplication on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86_64.scalarBase

end VG
