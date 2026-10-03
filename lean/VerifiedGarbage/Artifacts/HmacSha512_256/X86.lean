import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-SHA-512/256 (RFC 2104) on x86

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`). `init` sets both states' hash values with
SHA-512/256's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad`
word by word into their buffers, and absorbs each with one call of
SHA-512/256's verified compression function.

`finalize` calls SHA-512/256's verified streaming `finalize` for the inner
hash, then computes the outer hash with one call of SHA-512/256's verified
compression function, on a block it lays out word by word in `scratch`: the
outer key's hash value, the inner digest, its padding and length.
-/

namespace VG.Artifacts.HmacSha512_256.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := Proof.Pbkdf2.Md.X86.sha512_256M.hmacInit
    contract := Spec.Hmac.sha512_256I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_256_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := Proof.Pbkdf2.Md.X86.sha512_256M.hmacFin
    contract := Spec.Hmac.sha512_256I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha512_256.X86
