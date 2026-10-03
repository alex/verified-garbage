import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified

/-!
# Ed448 scalar arithmetic on x86-64

The signatures and documentation come from the reviewed Ed448 API. These
building blocks reduce and combine scalars modulo the subgroup order with
baseline integer instructions; they neither hash messages nor implement
signing by themselves.
-/

namespace VG.Artifacts.Ed448Scalar.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.scalarReduceApi with
    target := X86_64.target
    doc := Spec.Ed448.scalarReduceApi.doc (notes := ["Processes the input from the top, \
      a 64-bit word at a time, into a seven-word remainder: each step folds the bits above \
      2^446 back with one 64x224-bit product, then adds 2^448 - L and selects the sum or the \
      saved remainder with a carry mask. Callee-saved registers are saved in the first 48 \
      bytes of `scratch`, and the output's address in the next 8."])
    code := Impl.Ed448.X86_64.scalarReduce
    contract := Spec.Ed448.scalarReduceContract X86_64.abi
    verified := Proof.Ed448.X86_64.scalarReduce_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed448.scalarMulAddApi with
    target := X86_64.target
    doc := Spec.Ed448.scalarMulAddApi.doc (notes := ["Reduces `k`, `s` and `r` modulo L \
      as `vg_ed448_scalar_reduce` does, multiplies the first two by product scanning \
      (X448's field multiplication without its reduction), reduces the 14-word product the \
      same way, and adds the third with a last conditional subtraction. Callee-saved \
      registers are saved in the first 48 bytes of `scratch`, and the arguments' addresses \
      in the next 32."])
    code := Impl.Ed448.X86_64.scalarMulAdd
    contract := Spec.Ed448.scalarMulAddContract X86_64.abi
    verified := Proof.Ed448.X86_64.scalarMulAdd_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448Scalar.X86_64
