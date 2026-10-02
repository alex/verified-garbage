import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Proof.X448.AArch64.Verified
import VerifiedGarbage.Proof.X448.AArch64.Lit

/-! # X448 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := AArch64.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are sixteen 28-bit limbs, multiplied with `madd` and \
      reduced with `2^448 = 2^224 + 1` (mod p). Inversion uses an addition chain for `p - 2`."])
    code := Impl.X448.AArch64.x448
    contract := Spec.X448.x448Contract AArch64.abi
    verified := Proof.X448.AArch64.x448_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X448.AArch64
