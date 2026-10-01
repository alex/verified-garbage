import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified

namespace VG.Artifacts.Ed25519PublicKey.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.publicKeyApi with
    target := Arm.target
    doc := Spec.Ed25519.publicKeyApi.doc (notes := ["Includes SHA-512 of the seed, RFC 8032 pruning, \
      and base-point multiplication. The temporary seed hash and scalar are cleared before returning."])
    code := Impl.Ed25519.Arm.PublicKey.code
    contract := Spec.Ed25519.publicKeyContract Arm.abi 280
    stack := 280
    verified := Proof.Ed25519.Arm.PublicKey.publicKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519PublicKey.Arm
