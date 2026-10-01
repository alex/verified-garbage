import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified

namespace VG.Artifacts.Ed25519MulAdd.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarMulAddApi with
    target := X86.target
    doc := Spec.Ed25519.scalarMulAddApi.doc (notes := ["Computes the full 512-bit multiply-add \
      with 32-bit product columns, then reduces every input bit modulo the subgroup order. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."])
    code := Impl.Ed25519.X86.scalarMulAdd
    contract := Spec.Ed25519.scalarMulAddContract X86.abi
    verified := Proof.Ed25519.X86.scalarMulAdd_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]
end VG.Artifacts.Ed25519MulAdd.X86
