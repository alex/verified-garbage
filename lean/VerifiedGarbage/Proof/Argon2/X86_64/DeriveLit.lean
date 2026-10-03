import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapLit`. -/
section
/-! A checked literal for complete reference-index mapping. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ReferenceMap.code

end VG
end

/-! Checked literals for the entry point's fixed instruction shapes. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Derive.prepare
materialize_code Impl.Argon2.X86_64.FillSetup.code
materialize_code Impl.Argon2.X86_64.FillIterations.loop
materialize_code Impl.Argon2.X86_64.FinalReduction.code

end VG
