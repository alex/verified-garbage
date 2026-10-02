import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X448.X86
import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Proof.X448.X86.Lit

/-! # X448 (RFC 7748) on x86 (32-bit) -/

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := X86.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are twenty-eight 16-bit limbs, multiplied with `mul` and \
      reduced with `2^448 = 2^224 + 1` (mod p). Inversion uses an addition chain for `p - 2`."])
    code := Impl.X448.X86.x448
    contract := Spec.X448.x448Contract X86.abi
    verified := Proof.X448.X86.x448_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X448.X86
