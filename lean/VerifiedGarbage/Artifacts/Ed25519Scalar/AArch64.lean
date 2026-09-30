import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified

/-!
# Ed25519 scalar reduction on AArch64

The signature and documentation come from the reviewed Ed25519 API.
This primitive processes every input bit using baseline integer instructions
as part of the complete AArch64 signing and verification implementation.
-/

namespace VG.Artifacts.Ed25519Scalar.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarReduceApi with
    target := AArch64.target
    doc := Spec.Ed25519.scalarReduceApi.doc (notes := ["Processes all 512 input bits with \
      a four-word remainder, subtracting the subgroup order and selecting with a borrow mask. \
      Callee-saved registers are saved in the first 48 bytes of `scratch`."])
    code := Impl.Ed25519.AArch64.scalarReduce
    contract := Spec.Ed25519.scalarReduceContract AArch64.abi
    verified := Proof.Ed25519.AArch64.scalarReduce_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519Scalar.AArch64
