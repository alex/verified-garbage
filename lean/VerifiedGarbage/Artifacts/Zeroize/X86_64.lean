import VerifiedGarbage.Proof.Zeroize.X86_64

namespace VG.Artifacts.Zeroize.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.X86_64.zeroize
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Zeroize.X86_64
