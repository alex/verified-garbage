import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified

namespace VG.Artifacts.Ed25519PublicKey.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.publicKeyApi with
    target := X86.target
    doc := Spec.Ed25519.publicKeyApi.doc (notes := ["Includes SHA-512 of the seed, RFC 8032 pruning, \
      and base-point multiplication. The temporary seed hash and scalar are cleared before returning."])
    code := Impl.Ed25519.X86.PublicKey.publicKey
    contract := Spec.Ed25519.publicKeyContract X86.abi 280
    stack := 280
    verified := Proof.Ed25519.X86.PublicKey.publicKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519PublicKey.X86
