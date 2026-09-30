import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.PointDecode

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code recoverCandidate
materialize_code parityBlock := (.block (Impl.X25519.X86.freeze 64 ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock := (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block recoverSuccess : Prog isa)
materialize_code decodeHeadBlock := (.block (decodeY ++ canonicalY) : Prog isa)
end VG.Proof.Ed25519.X86
