import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit

/-! Checked literals for the complete base-point multiplication program and its engine. -/

namespace VG

materialize_code Impl.Ed25519.AArch64.scalarBaseEngine
materialize_code Impl.Ed25519.AArch64.scalarBase

end VG
