import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/
namespace VG.Artifacts.Ed25519MulAdd.Arm

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarMulAddApi with
    target := Arm.target
    doc := Spec.Ed25519.scalarMulAddApi.doc (notes := ["Computes the complete 512-bit \
      multiply-add before reducing modulo the subgroup order. All three input scalars \
      may use all 256 bits. Multiplication uses only the low 32-bit `mul` instruction \
      on 16-bit limbs. Callee-saved registers are saved in `scratch`."])
    code := Impl.Ed25519.Arm.scalarMulAdd
    contract := Spec.Ed25519.scalarMulAddContract Arm.abi
    verified := Proof.Ed25519.Arm.scalarMulAdd_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519MulAdd.Arm
