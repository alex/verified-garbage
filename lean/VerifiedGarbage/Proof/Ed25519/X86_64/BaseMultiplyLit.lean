import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed

/-! Checked literals for the precomputed variant and the pieces of its constant-time proof. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code baseBatchTable
materialize_code baseAccumulate16Lit := (baseAccumulate16 Impl.X25519.X86_64.baseline)
materialize_code baseAccumulate16AdxLit := (baseAccumulate16 Impl.X25519.X86_64.adx)
materialize_code baseMultiplyInitLit := (.block (baseMultiplyInit Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code baseMultiplyInitLitAdx := (.block (baseMultiplyInit Impl.X25519.X86_64.adx) : Prog isa)
end VG.Proof.Ed25519.X86_64

namespace VG
materialize_code scalarBase_precomputedLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
materialize_code scalarBase_precomputedAdxLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx)
end VG
