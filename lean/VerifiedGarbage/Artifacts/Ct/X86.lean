import VerifiedGarbage.Proof.Ct.X86

namespace VG.Artifacts.Ct.X86
open VG.X86

def artifacts : List Artifact := [
  { Spec.Ct.eqApi with
    target := target
    doc := Spec.Ct.eqApi.doc
    code := Impl.Ct.X86.eq
    contract := Spec.Ct.eqContract abi 4
    verified := Proof.Ct.X86.verified
    stack := 4
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]
end VG.Artifacts.Ct.X86
