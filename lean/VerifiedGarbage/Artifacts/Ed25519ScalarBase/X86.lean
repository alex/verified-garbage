import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified

namespace VG.Artifacts.Ed25519ScalarBase.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := X86.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Processes all 256 scalar bits with fixed loops \
      and masked point selection, then writes a canonical compressed point. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed25519.X86.scalarBase
    contract := Spec.Ed25519.scalarBaseContract X86.abi
    verified := Proof.Ed25519.X86.scalarBase_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]
end VG.Artifacts.Ed25519ScalarBase.X86
