import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X448.AArch64.Fast
import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit

/-! # X448 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := AArch64.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are eight 56-bit limbs. A multiplication keeps its \
      operands in registers and accumulates two-word coefficients with Karatsuba's identity for \
      `2^224` (48 products, 30 for a square), reduced with `2^448 = 2^224 + 1` (mod p); sums and \
      differences are not reduced. Each ladder step forms its sums and differences from the \
      conditionally swapped coordinates directly, and does four of its ten products as two pairs \
      of AdvSIMD multiplications (sixteen 28-bit limbs, the two products in the two 64-bit lanes), \
      each interleaved with scalar operations independent of it. Inversion uses an addition chain \
      for `p - 2`."])
    code := Impl.X448.AArch64.Fast.x448
    contract := Spec.X448.x448Contract AArch64.abi
    verified := Proof.X448.AArch64.Fast.x448_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X448.AArch64
