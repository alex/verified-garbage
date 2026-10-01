import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := AArch64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      a comb: the scalar's 64 nibbles n give the digits n - 8, and each digit's multiple of \
      [16^i]B is one of 32 tables of [k 256^j]B for k <= 8, affine, cached as \
      [Y - X, Y + X, 2dT] in immediates and checked against the specification in Lean, \
      selected by reading every candidate under masks and negated under the digit's sign \
      mask: 65 additions and four doublings, in a fixed schedule. The working values and \
      saved registers reside in `scratch`."])
    code := Impl.Ed25519.AArch64.scalarBase
    contract := Spec.Ed25519.scalarBaseContract AArch64.abi
    verified := Proof.Ed25519.AArch64.scalarBase_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519ScalarBase.AArch64
