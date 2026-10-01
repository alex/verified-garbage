import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed

/-! Checked literals for the precomputed variant and its initialization. -/
namespace VG
materialize_code Impl.Ed25519.X86_64.scalarBase_precomputed
materialize_code Impl.Ed25519.X86_64.baseMultiplyPrecomputedInit
end VG
