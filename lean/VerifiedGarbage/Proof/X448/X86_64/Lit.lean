import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X448.X86_64

/-!
# X448 on x86-64: the code as a literal

Untrusted: everything here is checked by Lean. Materializing the code once
avoids rebuilding the unrolled arithmetic in each kernel-evaluated check.
-/

namespace VG

materialize_code Impl.X448.X86_64.x448

end VG
