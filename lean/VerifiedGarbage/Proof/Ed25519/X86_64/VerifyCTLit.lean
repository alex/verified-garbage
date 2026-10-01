import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-! Checked literals for the verifier's fixed control-flow pieces. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

materialize_code recoverCandidateLit := (recoverCandidate Impl.X25519.X86_64.baseline : Prog isa)
materialize_code recoverCandidateAdxLit := (recoverCandidate Impl.X25519.X86_64.adx : Prog isa)
materialize_code decodeLoadBlock := (.block pointDecodeLoad : Prog isa)
materialize_code parityBlock :=
  (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual Impl.X25519.X86_64.baseline 11 6) : Prog isa)
materialize_code rootCheckBlockAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual Impl.X25519.X86_64.baseline 11 12) : Prog isa)
materialize_code rootCheckMinusBlockAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode Impl.X25519.X86_64.baseline [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code negateBlockAdx := (.block (fieldCode Impl.X25519.X86_64.adx [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock :=
  (.block (fieldCode Impl.X25519.X86_64.baseline [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code rootAdjustBlockAdx :=
  (.block (fieldCode Impl.X25519.X86_64.adx [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block (recoverSuccess Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code successBlockAdx := (.block (recoverSuccess Impl.X25519.X86_64.adx) : Prog isa)
materialize_code pointEqualFirst := (.block (fieldCode Impl.X25519.X86_64.baseline pointEqualOps ++ fieldEqual Impl.X25519.X86_64.baseline 8 9) : Prog isa)
materialize_code pointEqualFirstAdx := (.block (fieldCode Impl.X25519.X86_64.adx pointEqualOps ++ fieldEqual Impl.X25519.X86_64.adx 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual Impl.X25519.X86_64.baseline 10 11) : Prog isa)
materialize_code pointEqualSecondAdx := (.block (fieldEqual Impl.X25519.X86_64.adx 10 11) : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7424) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7552) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyScalarTail := (.block (loadScalarWords ++ scalarSubtract) : Prog isa)
materialize_code verifyFinishBlock :=
  (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore) : Prog isa)
materialize_code windowPrepLit :=
  (.seq (.seq (.seq (.block windowSetup) (aTable Impl.X25519.X86_64.baseline)) (.block bTable)) (.block (windowInit Impl.X25519.X86_64.baseline)) : Prog isa)
materialize_code windowPrepLitAdx :=
  (.seq (.seq (.seq (.block windowSetup) (aTable Impl.X25519.X86_64.adx)) (.block bTable)) (.block (windowInit Impl.X25519.X86_64.adx)) : Prog isa)
materialize_code double4Lit := (double4 Impl.X25519.X86_64.baseline : Prog isa)
materialize_code double4AdxLit := (double4 Impl.X25519.X86_64.adx : Prog isa)
materialize_code addDigitA :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd Impl.X25519.X86_64.baseline)) :
    Prog isa)
materialize_code addDigitAAdx :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd Impl.X25519.X86_64.adx)) :
    Prog isa)
materialize_code addDigitB :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
    (pointAddCached Impl.X25519.X86_64.baseline)) : Prog isa)
materialize_code addDigitBAdx :=
  (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
    (pointAddCached Impl.X25519.X86_64.adx)) : Prog isa)
materialize_code negRBlock := (.block (negR Impl.X25519.X86_64.baseline) : Prog isa)
materialize_code negRBlockAdx := (.block (negR Impl.X25519.X86_64.adx) : Prog isa)

end VG.Proof.Ed25519.X86_64
