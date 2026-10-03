import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# ECDSA signature verification over P-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p256_verify`, in the
module `ecdsa_p256`, for P-256's `Ecdsa.Instance`.
-/

namespace VG.Spec.Ecdsa.P256

/-- `vg_ecdsa_p256_verify` on every target. -/
def verifyApi : Api := inst.verifyApi

end VG.Spec.Ecdsa.P256
