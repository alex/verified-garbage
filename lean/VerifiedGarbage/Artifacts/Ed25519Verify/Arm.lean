import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/
namespace VG.Artifacts.Ed25519Verify.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := Arm.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. Point decoding branches depend only on public inputs. \
      Point tables and saved registers reside in `scratch`."])
    code := Impl.Ed25519.Arm.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract Arm.abi
    verified := Proof.Ed25519.Arm.verify_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519Verify.Arm
