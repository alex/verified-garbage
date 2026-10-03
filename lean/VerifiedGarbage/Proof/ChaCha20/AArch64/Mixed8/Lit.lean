import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8

namespace VG
materialize_code ChaCha20.AArch64.Mixed8.xorNeon := Impl.ChaCha20.AArch64.Mixed8.xor false
materialize_code ChaCha20.AArch64.Mixed8.xorSve2 := Impl.ChaCha20.AArch64.Mixed8.xor true
end VG
