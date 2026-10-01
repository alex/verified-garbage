import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4

namespace VG

/- Cache the kernel-checked four-block stream code for all caller audits. -/
materialize_code Impl.ChaCha20.AArch64.Neon4.xor

end VG
