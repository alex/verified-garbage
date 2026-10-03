import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha256_sign`, calling
HMAC-SHA-256's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-256 variant carried by `MdHash.sha256`, named with
its suffix (e.g. `vg_ecdsa_p256_sha256_sign_shani`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 160 bytes: a 136-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p256_sign` only its return address).
-/

namespace VG.Generic.MdHash.X86_64.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_verified sign_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P256Sha256.signApi with
      name := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.doc (notes := ["Computes `h = bits2octets(digest)` \
        by a conditional subtraction of `n`, and each HMAC with `" ++ (cfgOf c).H.hmacInitN ++ "`, `" ++
        (cfgOf c).H.updN ++ "` and `" ++ (cfgOf c).H.hmacFinN ++ "`, using the start of `scratch` for \
        HMAC's states and working space and the message. Each candidate `k = V` is tried with \
        `vg_ecdsa_p256_sign`, which uses all of `scratch`; whether to try another is computed \
        without branches from its result and the count of candidates left, so the code branches \
        only on that. `K`, `V`, `h`, the count and the pointers are kept in a 136-byte stack frame, \
        whose secrets are cleared before it is popped; the calls use the 24 bytes below it."])
      code := (cfgOf c).sign
      contract := Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 160
      stack := 160
      verified := sign_verified c
      spSafe := sign_spSafe c
      features := c.features }]

end VG.Generic.MdHash.X86_64.EcdsaP256Sha256
