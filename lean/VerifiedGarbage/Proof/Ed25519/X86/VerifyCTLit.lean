import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Verify

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code pointEqualFirst := (.block (fieldCode pointEqualOps ++ fieldEqual 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual 10 11) : Prog isa)
materialize_code verifyCombineBlock := (.block verifyCombine : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
materialize_code verifyBasePoint := (.block (constPoint Spec.Ed25519.basePoint) : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7680) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7808) : Prog isa)
materialize_code verifyWriteLhs := (.block (pointTableWrite 7936) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7680) : Prog isa)
materialize_code verifyScalarTail := (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr)) : Prog isa)
materialize_code verifyLoadWords := (.block (copyWords 96 8) : Prog isa)
materialize_code verifyPrepare32 := (.block (expandScalarBits 32 ++ fieldCode [.const 16 Spec.Ed25519.d]) : Prog isa)
materialize_code verifyPrepare64 := (.block (expandScalarBits 64 ++ fieldCode [.const 16 Spec.Ed25519.d]) : Prog isa)
end VG.Proof.Ed25519.X86
