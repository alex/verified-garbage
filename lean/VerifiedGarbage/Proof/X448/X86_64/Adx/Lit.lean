import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X448.X86_64.Adx

/-!
# X448 on x86-64 with BMI2 and ADX: the code as a literal
-/

namespace VG

materialize_code Impl.X448.X86_64.x448Adx

end VG
