import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified

namespace VG.Artifacts.Ed25519VerifyMessage.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyApi with
    target := Arm.target
    doc := Spec.Ed25519.verifyApi.doc (notes := ["Includes SHA-512 of R || A || message, challenge \
      reduction, and strict verification of the Ed25519 equation."])
    code := Impl.Ed25519.Arm.VerifyMessage.code
    contract := Spec.Ed25519.verifyContract Arm.abi 280
    stack := 280
    verified := Proof.Ed25519.Arm.VerifyMessage.verifyMessage_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519VerifyMessage.Arm
