import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase

/-! Checked literals for the pieces of the constant-time proof of base-point multiplication. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
materialize_code baseBatchTable
materialize_code baseAccumulate16
materialize_code baseMultiplyInitLit := (.block baseMultiplyInit : Prog isa)
end VG.Proof.Ed25519.AArch64
