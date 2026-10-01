import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64

namespace VG
materialize_code Impl.Poly1305.AArch64.Radix64.blocks
materialize_code Impl.Poly1305.AArch64.Radix64.update
materialize_code Impl.Poly1305.AArch64.Radix64.finalize
end VG
