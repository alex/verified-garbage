import VerifiedGarbage.Proof.Ct.AArch64

namespace VG.Artifacts.Ct.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Ct.eqApi with
    target := target
    doc := Spec.Ct.eqApi.doc
    code := Impl.Ct.AArch64.eq
    contract := Spec.Ct.eqContract abi
    verified := Proof.Ct.AArch64.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Ct.AArch64
