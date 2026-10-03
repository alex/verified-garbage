import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224

/-!
# PBKDF2-HMAC-SHA-224 (RFC 8018) on x86, for every x86 SHA-256 backend: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): each step is two calls of the backend's
verified SHA-256 compression function, on a block laid out once, word by
word, in `scratch` (`U`, its padding and length), starting from the key's
inner and outer hash values.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling SHA-224's `init`, the backend's
SHA-256 streaming functions, HMAC-SHA-224's `init` and `finalize` and the
iteration above, made with the backend. `stack` is that of the shared
contracts: 48 bytes for the iteration, and 76 for `pbkdf2`, which pushes up
to 24 bytes of arguments for the functions it calls, and their return
address, and gives them 48.
-/

namespace VG.Generic.Sha256.X86.Pbkdf2Sha224

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha224I.iterateApi with
    name := Spec.Hmac.sha224I.iterateApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.iterateApi.doc
    code := v.M224.iterate
    contract := Spec.Hmac.sha224I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 48
    verified := v.iterate224
    spSafe := v.iter224Sp
    features := v.features },
  { Spec.Hmac.sha224I.pbkdf2Api with
    name := Spec.Hmac.sha224I.pbkdf2Api.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha224I.pbkdf2Api.doc
    code := v.F224.pbkdf2
    contract := Spec.Hmac.sha224I.pbkdf2Contract X86.abi 76
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.sha224_verified v
    spSafe := v.pbkdf2_224Sp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2Sha224
