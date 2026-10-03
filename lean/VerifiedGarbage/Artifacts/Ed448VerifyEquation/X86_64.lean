import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified

/-!
# Ed448 verification's equation on x86-64

The signature and documentation come from the reviewed Ed448 API.
-/

namespace VG.Artifacts.Ed448VerifyEquation.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.verifyEquationApi with
    target := X86_64.target
    doc := Spec.Ed448.verifyEquationApi.doc (notes := ["Uses baseline integer instructions, \
      and runs the same operations whatever the inputs: the checks (the encodings of A and R, \
      S < L, and the comparison) are accumulated in one word of `scratch`, 0 exactly when \
      all pass. Decodes A with RFC 8032's square root (X448's addition chain up to \
      z^(2^223 - 1), then 223 squarings) and negates it; computes [S]B + [k](-A) with one \
      chain of doublings, adding B and -A for every bit of S and k and swapping each sum in \
      with a mask of the bit; then compares [4] of it with [4]R projectively. Field elements \
      are X448's seven 64-bit words, multiplied with `mul` by columns. Callee-saved \
      registers are saved in the first 48 bytes of `scratch`."])
    code := Impl.Ed448.X86_64.verifyEquation
    contract := Spec.Ed448.verifyEquationContract X86_64.abi
    verified := Proof.Ed448.X86_64.verifyEquation_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448VerifyEquation.X86_64
