import VerifiedGarbage.Proof.Ct.PPC64LE

namespace VG.Artifacts.Ct.PPC64LE
open VG.PPC64LE

def artifacts : List Artifact := [
  { Spec.Ct.eqApi with
    target := target
    doc := Spec.Ct.eqApi.doc
    code := Impl.Ct.PPC64LE.eq
    contract := Spec.Ct.eqContract abi
    verified := Proof.Ct.PPC64LE.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Ct.PPC64LE
