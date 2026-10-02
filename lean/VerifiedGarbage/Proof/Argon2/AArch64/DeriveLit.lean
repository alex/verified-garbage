import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressLit
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.AArch64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.AArch64.AddressHeaderLit
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit
import VerifiedGarbage.Proof.Framework.Lit

/-! Checked literals for the entry point's fixed instruction shapes. -/

namespace VG

materialize_code Impl.Argon2.AArch64.Derive.prepare
materialize_code Impl.Argon2.AArch64.FillSetup.code
materialize_code Impl.Argon2.AArch64.FillIterations.loop
materialize_code Impl.Argon2.AArch64.FinalReduction.code

end VG
