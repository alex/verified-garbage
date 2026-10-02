import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress

/-! Checked literals for compression and the enclosing argument setup. -/

namespace VG

materialize_code Impl.Argon2.AArch64.FillCompress.operation
materialize_code Impl.Argon2.AArch64.FillCompress.code

end VG
