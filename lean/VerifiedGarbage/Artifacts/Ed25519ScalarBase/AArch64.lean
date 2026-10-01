import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := AArch64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      the 256 powers [2^i]B of the base point, precomputed as [Y - X, Y + X, 2dT, 2Z] and \
      checked against the specification in Lean. All 256 scalar bits follow a fixed schedule; \
      point tables and saved registers reside in `scratch`."])
    code := Impl.Ed25519.AArch64.scalarBase
    contract := Spec.Ed25519.scalarBaseContract AArch64.abi
    verified := Proof.Ed25519.AArch64.scalarBase_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519ScalarBase.AArch64
