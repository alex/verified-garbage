import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified

namespace VG.Artifacts.Ed25519Scalar.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarReduceApi with
    target := X86.target
    doc := Spec.Ed25519.scalarReduceApi.doc (notes := ["Processes all 512 input bits using \
      eight 32-bit remainder words, a fixed byte loop, and masked subtraction of the subgroup order. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed25519.X86.scalarReduce
    contract := Spec.Ed25519.scalarReduceContract X86.abi
    verified := Proof.Ed25519.X86.scalarReduce_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]
end VG.Artifacts.Ed25519Scalar.X86
