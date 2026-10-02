import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified

/-!
# Ed25519 scalar reduction on x86-64

The signature and documentation come from the reviewed Ed25519 API.
This building block reduces a 64-bit word at a time using baseline integer
instructions; it neither hashes messages nor implements signing by itself.
-/

namespace VG.Artifacts.Ed25519Scalar.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarReduceApi with
    target := X86_64.target
    doc := Spec.Ed25519.scalarReduceApi.doc (notes := ["Processes the eight input words \
      from the top into a four-word remainder: each step folds the bits above 2^252 back with \
      one 64x128-bit product, then subtracts the subgroup order and selects with a borrow mask. \
      Callee-saved registers are saved in the first 48 bytes of `scratch`, and the output's \
      address in the next 8."])
    code := Impl.Ed25519.X86_64.scalarReduce
    contract := Spec.Ed25519.scalarReduceContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarReduce_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Scalar.X86_64
