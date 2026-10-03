import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched

/-!
# ChaCha20-Poly1305 on AArch64: the code as literals
-/

namespace VG

materialize_code Impl.ChaCha20Poly1305.AArch64.seal
materialize_code Impl.ChaCha20Poly1305.AArch64.open
materialize_code ChaCha20Poly1305.AArch64.sealScalar :=
  Impl.ChaCha20Poly1305.AArch64.sealCode .scalar false
materialize_code ChaCha20Poly1305.AArch64.openScalar :=
  Impl.ChaCha20Poly1305.AArch64.openCode .scalar false
materialize_code ChaCha20Poly1305.AArch64.sealNeon :=
  Impl.ChaCha20Poly1305.AArch64.sealCode .neon true
materialize_code ChaCha20Poly1305.AArch64.openNeon :=
  Impl.ChaCha20Poly1305.AArch64.openCode .neon true

end VG
