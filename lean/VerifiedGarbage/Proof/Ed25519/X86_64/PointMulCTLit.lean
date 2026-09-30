import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Checked literals for the pieces of the relational constant-time proof. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code prepareBatch
materialize_code accumulate16
materialize_code pointEncode
materialize_code scalarBasePrepare
materialize_code pointMultiplyInit16 := pointMultiplyInit 16
materialize_code baseInit := (.block scalarBaseInit : Prog isa)
materialize_code identityInit := (.block (constPoint Spec.Ed25519.identity) : Prog isa)

end VG.Proof.Ed25519.X86_64
