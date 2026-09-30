import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

namespace VG.Artifacts.Ed25519Verify.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := X86_64.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. No additional subgroup or small-order policy is imposed."])
    code := Impl.Ed25519.X86_64.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Verify.X86_64
