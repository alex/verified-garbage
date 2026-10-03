import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-256
(`Spec/Ecdsa/P256.lean`) with SHA-384: `vg_ecdsa_p256_sha384_sign`, in the
module `ecdsa_p256_sha384`. The hash is 48 bytes; `bits2int` takes its
leftmost 256 bits (RFC 6979 §2.3.2), as FIPS 186-5 does. At most 8
candidates, as with SHA-256 (`P256Sha256.lean`): each is unsuitable with
probability under `2^-31` (`n > 2^256 - 2^224`), so all 8 with probability
under `2^-248`.
-/

namespace VG.Spec.Ecdsa.Rfc6979.P256Sha384

/-- P-256 with HMAC-SHA-384. -/
def inst : Instance where
  ecdsa := Ecdsa.P256.inst
  hash := Hmac.sha384
  hashLen := 48
  hashName := "sha384"
  hashTitle := "SHA-384"
  tries := 8

/-- `vg_ecdsa_p256_sha384_sign` on every target. -/
def signApi : Api := inst.signApi

end VG.Spec.Ecdsa.Rfc6979.P256Sha384
