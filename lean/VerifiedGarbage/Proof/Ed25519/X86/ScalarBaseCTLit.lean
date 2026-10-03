import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code baseStartBlock := (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps) : Prog isa)
materialize_code baseFinishTail := (.block (outputWords 96 8 ++ Impl.X25519.X86.restore) : Prog isa)
end VG.Proof.Ed25519.X86
