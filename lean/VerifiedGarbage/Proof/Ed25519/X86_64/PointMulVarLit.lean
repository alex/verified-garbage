import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-! Checked literals for the variable-time multiplications' constant-time proofs. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code addEntryExact := (.block (addEntry pointAdd) : Prog isa)
materialize_code addEntryCached := (.block (addEntry pointAddCached) : Prog isa)
materialize_code varBitBlock :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ scalarBitTest) : Prog isa)

end VG.Proof.Ed25519.X86_64
