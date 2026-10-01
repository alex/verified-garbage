import VerifiedGarbage.Proof.Ct.X86_64

namespace VG.Artifacts.Ct.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  { Spec.Ct.eqApi with
    target := target
    doc := Spec.Ct.eqApi.doc
    code := Impl.Ct.X86_64.eq
    contract := Spec.Ct.eqContract abi
    verified := Proof.Ct.X86_64.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Ct.X86_64
