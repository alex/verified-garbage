import VerifiedGarbage.Proof.Zeroize.Arm

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.Arm.zeroize
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.Arm.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Zeroize.Arm
