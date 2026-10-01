import VerifiedGarbage.Proof.Ct.Arm

namespace VG.Artifacts.Ct.Arm
open VG.Arm

def artifacts : List Artifact := [
  { Spec.Ct.eqApi with
    target := target
    doc := Spec.Ct.eqApi.doc
    code := Impl.Ct.Arm.eq
    contract := Spec.Ct.eqContract abi 4
    verified := Proof.Ct.Arm.verified
    stack := 4
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Ct.Arm
