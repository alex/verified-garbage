import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified

namespace VG.Artifacts.Ed25519SignCached.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.signCachedApi with
    target := Arm.target
    doc := Spec.Ed25519.signCachedApi.doc (notes := ["Includes SHA-512, scalar reduction, \
      base-point multiplication, and scalar multiply-add. Secret intermediate buffers are cleared before returning."])
    code := Impl.Ed25519.Arm.SignCached.code
    contract := Spec.Ed25519.signCachedContract Arm.abi 280
    stack := 280
    verified := Proof.Ed25519.Arm.SignCached.signCached_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519SignCached.Arm
