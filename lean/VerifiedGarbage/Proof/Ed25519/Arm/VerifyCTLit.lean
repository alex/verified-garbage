import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit

/-! Checked code literals for verifier composition. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code verifyBasePoint := constPoint Spec.Ed25519.basePoint
materialize_code verifyWriteA := (.block (pointTableWrite 7744) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7872) : Prog isa)
materialize_code verifyWriteLhs := (.block (pointTableWrite 8000) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7744) : Prog isa)
materialize_code verifyCombine
materialize_code verifyScalarTail := (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr)) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
end VG.Proof.Ed25519.Arm
