import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-! # ECDSA verification over P-256 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verify Impl.Ecdsa.X86_64.p256

end VG.Impl.Ecdsa.Verify.X86_64
