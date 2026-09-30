import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar

/-! The kernel checks this literal once; taint and instruction checks reuse it. -/
namespace VG
materialize_code Impl.Ed25519.AArch64.scalarReduce
end VG
