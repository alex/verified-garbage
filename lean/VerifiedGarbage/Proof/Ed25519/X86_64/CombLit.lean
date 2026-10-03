import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectTable
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit

/-! Checked literals for the comb variant and its constant-time proof. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64
materialize_code combMultiplyLit := (combMultiply Impl.X25519.X86_64.baseline)
materialize_code combMultiplyAdxLit := (combMultiply Impl.X25519.X86_64.adx)
end VG.Proof.Ed25519.X86_64

namespace VG
materialize_code scalarBase_precomputedLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
materialize_code scalarBase_precomputedAdxLit := (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx)
end VG
