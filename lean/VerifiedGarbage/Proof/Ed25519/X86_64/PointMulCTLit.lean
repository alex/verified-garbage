import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Checked literals for the pieces of the relational constant-time proof. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code prepareBatchLit := (prepareBatch Impl.X25519.X86_64.baseline : Prog isa)
materialize_code prepareBatchAdxLit := (prepareBatch Impl.X25519.X86_64.adx : Prog isa)
materialize_code accumulate16Lit := (accumulate16 Impl.X25519.X86_64.baseline : Prog isa)
materialize_code accumulate16AdxLit := (accumulate16 Impl.X25519.X86_64.adx : Prog isa)
materialize_code pointEncodeLit := (pointEncode Impl.X25519.X86_64.baseline : Prog isa)
materialize_code pointEncodeAdxLit := (pointEncode Impl.X25519.X86_64.adx : Prog isa)
materialize_code scalarBasePrepareLit := (scalarBasePrepare Impl.X25519.X86_64.baseline : Prog isa)
materialize_code scalarBasePrepareAdxLit := (scalarBasePrepare Impl.X25519.X86_64.adx : Prog isa)
materialize_code pointMultiplyInit16 := pointMultiplyInit Impl.X25519.X86_64.baseline 16
materialize_code pointMultiplyInit16Adx := pointMultiplyInit Impl.X25519.X86_64.adx 16
materialize_code baseInit := (.block (scalarBaseInit Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code baseInitAdx := (.block (scalarBaseInit Impl.X25519.X86_64.adx) : Prog isa)
materialize_code identityInit := (.block (constPoint Impl.X25519.X86_64.baseline Spec.Ed25519.identity) : Prog isa)
materialize_code identityInitAdx := (.block (constPoint Impl.X25519.X86_64.adx Spec.Ed25519.identity) : Prog isa)

end VG.Proof.Ed25519.X86_64
