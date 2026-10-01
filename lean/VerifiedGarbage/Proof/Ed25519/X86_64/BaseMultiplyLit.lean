import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed

/-! Checked literals for the precomputed variant and the pieces of its constant-time proof. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code baseBatchTable
materialize_code baseAccumulate16
materialize_code baseMultiplyInitLit := (.block baseMultiplyInit : Prog isa)
end VG.Proof.Ed25519.X86_64

namespace VG
materialize_code Impl.Ed25519.X86_64.scalarBase_precomputed
end VG
