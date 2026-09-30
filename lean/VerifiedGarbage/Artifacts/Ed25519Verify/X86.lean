import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified

/-! The complete strict verification equation on baseline i686. -/
namespace VG.Artifacts.Ed25519Verify.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := X86.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Checks canonical point encodings and S < L, \
      then evaluates the uncofactored equation using all 512 challenge bits. \
      Point decoding branches depend only on public inputs. Point tables and \
      callee-saved registers reside in `scratch`; no stack allocation is needed."])
    code := Impl.Ed25519.X86.verifyEquation
    contract := Spec.Ed25519.verifyEquationContract X86.abi
    verified := Proof.Ed25519.X86.verify_verified
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Verify.X86
