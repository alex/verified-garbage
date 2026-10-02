import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified

/-! # ML-DSA (FIPS 204) signing on AArch64 -/

namespace VG.Generic.Keccak.AArch64.MlDsaSign

open VG
open VG.Proof.MlDsa.AArch64.Sign (primsWith)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and its return address in `scratch`; \
    the frames of its calls use the 16 bytes of stack below the stack pointer.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.sign44Api with
    name := Spec.MlDsa.sign44Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.sign44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Sign.signWith v.callee (primsWith v.callee) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.sign44_verifiedWith' (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sign65Api with
    name := Spec.MlDsa.sign65Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.sign65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Sign.signWith v.callee (primsWith v.callee) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.sign65_verifiedWith' (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sign87Api with
    name := Spec.MlDsa.sign87Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.sign87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Sign.signWith v.callee (primsWith v.callee) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.sign87_verifiedWith' (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlDsaSign
