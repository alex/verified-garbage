import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-! Checked literals for the verifier's fixed control-flow pieces. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code recoverCandidate
materialize_code decodeLoadBlock := (.block pointDecodeLoad : Prog isa)
materialize_code parityBlock :=
  (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock :=
  (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block recoverSuccess : Prog isa)
materialize_code pointEqualFirst := (.block (fieldCode pointEqualOps ++ fieldEqual 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual 10 11) : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7424) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7552) : Prog isa)
materialize_code verifyWriteLhs := (.block (pointTableWrite 7680) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7424) : Prog isa)
materialize_code verifyCombineBlock := (.block verifyCombine : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyScalarTail := (.block (loadScalarWords ++ scalarSubtract) : Prog isa)
materialize_code verifyFinishBlock :=
  (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore) : Prog isa)
materialize_code pointMultiplyInit32 := pointMultiplyInit 32
materialize_code scalarPrepare16 :=
  (.seq (scalarBits 32) (.block (constField 16 Spec.Ed25519.d)) : Prog isa)
materialize_code scalarPrepare32 :=
  (.seq (scalarBits 64) (.block (constField 16 Spec.Ed25519.d)) : Prog isa)

end VG.Proof.Ed25519.X86_64
