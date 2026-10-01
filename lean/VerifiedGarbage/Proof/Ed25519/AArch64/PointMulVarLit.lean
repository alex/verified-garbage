import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.PointMulVar

/-! Checked literals for the variable-time multiplications' constant-time proofs. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

materialize_code addEntryExact := (.block (addEntry pointAdd) : Prog isa)
materialize_code addEntryCached := (.block (addEntry pointAddCached) : Prog isa)
materialize_code varBitBlock :=
  (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ scalarBitLoad) : Prog isa)

end VG.Proof.Ed25519.AArch64
