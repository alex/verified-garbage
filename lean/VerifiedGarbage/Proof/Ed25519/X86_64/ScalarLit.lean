import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Scalar

/-! The kernel checks this literal once; taint and instruction checks reuse it. -/

namespace VG

materialize_code Impl.Ed25519.X86_64.scalarReduce

end VG
