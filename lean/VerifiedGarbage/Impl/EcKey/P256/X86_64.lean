import VerifiedGarbage.Impl.EcKey.X86_64
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-! # P-256 public keys on x86-64: four-word field elements and scalars -/

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86_64.p256

end VG.Impl.EcKey.X86_64
