import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified

/-!
# ML-DSA (FIPS 204) on x86-64: signing

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call an
implementation `v` of the polynomial arithmetic (`vg_mldsa_ntt`, …), are
emitted once for each implementation (`Variants/MlDsaArith/X86_64/`), named
with its suffix (e.g. `vg_mldsa44_sign_avx2`), and need its CPU features.
-/

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSign

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 \
    bytes of stack below its return address.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts (v : ArithImpl) : List Artifact := [
  { Spec.MlDsa.sign44Api with
    name := Spec.MlDsa.sign44Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.sign44Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa44 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inl rfl)
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl) },
  { Spec.MlDsa.sign65Api with
    name := Spec.MlDsa.sign65Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.sign65Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa65 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inr (.inl rfl))
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl)) },
  { Spec.MlDsa.sign87Api with
    name := Spec.MlDsa.sign87Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.sign87Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa87 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inr (.inr rfl))
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl)) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSign
