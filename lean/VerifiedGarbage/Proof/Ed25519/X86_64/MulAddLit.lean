import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.MulAdd

/-! A checked code literal for the taint, ABI, and stack-pointer audits. -/

namespace VG

materialize_code Impl.Ed25519.X86_64.scalarMulAdd

end VG
