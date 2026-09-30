import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

namespace VG.Artifacts.Ed25519Verify.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := AArch64.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. No additional subgroup or small-order policy is imposed."])
    code := Impl.Ed25519.AArch64.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract AArch64.abi
    verified := Proof.Ed25519.AArch64.verify_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519Verify.AArch64
