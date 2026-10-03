import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-! # ECDH over P-256 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p256

end VG.Impl.Ecdh.X86_64
