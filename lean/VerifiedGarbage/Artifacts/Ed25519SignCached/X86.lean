import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Verified

namespace VG.Artifacts.Ed25519SignCached.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.signCachedApi with
    target := X86.target
    doc := Spec.Ed25519.signCachedApi.doc (notes := ["Includes SHA-512, scalar reduction, \
      base-point multiplication, and scalar multiply-add. Secret intermediate buffers are cleared before returning."])
    code := Impl.Ed25519.X86.SignCached.code
    contract := Spec.Ed25519.signCachedContract X86.abi 280
    stack := 280
    verified := Proof.Ed25519.X86.SignCached.signCached_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519SignCached.X86
