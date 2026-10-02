import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.X448.AArch64.Weak

/-!
# X448 on AArch64: the code as a literal

Untrusted: everything here is checked by Lean. Materializing the weak-field code once
avoids rebuilding the unrolled arithmetic in each kernel-evaluated check.
-/

namespace VG

materialize_code Impl.X448.AArch64.Weak.x448

end VG
