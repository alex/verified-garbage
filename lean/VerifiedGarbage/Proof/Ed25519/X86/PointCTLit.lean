import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86.Field
import VerifiedGarbage.Impl.Ed25519.X86.Power

/-! The point arithmetic and the inversion chain as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/
namespace VG.Impl.Ed25519.X86

materialize_value pointAdd
materialize_value pointDouble
materialize_code power250
materialize_code invert
materialize_code rootPower

end VG.Impl.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code pointEncode
materialize_code accumulate16
materialize_code powersBody16 := powersBody 1024 16 true
materialize_code powersBody32 := powersBody 1024 32 true
materialize_code powersBodyLocal := powersBody 5120 16 false
materialize_code checkpointBlock := (.block loadCheckpoint : Prog isa)
materialize_code restoreBlock := (.block restorePoint : Prog isa)
materialize_code identityBlock := (.block (constPoint Spec.Ed25519.identity) : Prog isa)
end VG.Proof.Ed25519.X86
