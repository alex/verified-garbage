import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.P256

/-!
# ECDSA over P-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-256
(`Spec/P256.lean`): `vg_ecdsa_p256_sign`, in the module `ecdsa_p256`.
-/

namespace VG.Spec.Ecdsa.P256

/-- P-256. -/
def inst : Instance where
  curve := Spec.P256.curve
  name := "p256"
  title := "P-256"

/-- `vg_ecdsa_p256_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.P256
