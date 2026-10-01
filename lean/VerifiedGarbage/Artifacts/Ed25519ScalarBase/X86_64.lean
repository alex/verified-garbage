import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions \
      and a fixed schedule for all 256 input bits. Point tables and saved registers \
      reside in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarBase
    contract := Spec.Ed25519.scalarBaseContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarBase_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    name := "vg_ed25519_scalar_base_precomputed"
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      sixteen precomputed checkpoints, checked against the specification in Lean. \
      All 256 scalar bits follow a fixed schedule; point tables and saved registers reside in `scratch`."])
    code := Impl.Ed25519.X86_64.scalarBase_precomputed
    contract := Spec.Ed25519.scalarBaseContract X86_64.abi
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519ScalarBase.X86_64
