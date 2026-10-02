import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress

/-! Checked literals for compression and the enclosing argument setup. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillCompress.operation
materialize_code Impl.Argon2.X86_64.FillCompress.code

end VG
