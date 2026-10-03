import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# HMAC-SHA-224 (RFC 2104) on x86, for every x86 SHA-256 backend

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of the backend's
verified SHA-256 compression function.

`finalize` calls the backend's verified SHA-256 streaming `finalize` for the
inner hash, then computes the outer hash with one call of the backend's
verified compression function, on a block it lays out word by word in
`scratch`: the outer key's hash value, the inner digest (the first 28 bytes
of the inner final hash value), its padding and length.
-/

namespace VG.Generic.Sha256.X86.HmacSha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha224I.initApi with
    name := Spec.Hmac.sha224I.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.initApi.doc
    code := v.M224.hmacInit
    contract := Spec.Hmac.sha224I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := v.hmacInit224
    spSafe := v.init224Sp
    features := v.features },
  { Spec.Hmac.sha224I.finalizeApi with
    name := Spec.Hmac.sha224I.finalizeApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.finalizeApi.doc
    code := v.M224.hmacFin
    contract := Spec.Hmac.sha224I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := v.hmacFin224
    spSafe := v.fin224Sp
    features := v.features }]

end VG.Generic.Sha256.X86.HmacSha224
