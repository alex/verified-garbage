import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite

/-! Checked literal of the complete copy/XOR block write. -/

namespace VG

materialize_code Impl.Argon2.X86_64.FillWrite.code

end VG
