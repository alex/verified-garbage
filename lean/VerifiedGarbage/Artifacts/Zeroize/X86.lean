import VerifiedGarbage.Proof.Zeroize.X86

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.X86.zeroize
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.X86.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Zeroize.X86
