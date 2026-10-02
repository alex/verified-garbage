import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst

/-! # ML-DSA (FIPS 204) verification on AArch64 -/

namespace VG.Generic.Keccak.AArch64.MlDsaVerify

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results are combined \
    without a branch, so the only branches depend on the public key and the signature."]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.verify44Api with
    name := Spec.MlDsa.verify44Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verify44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify44With v.callee
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify44_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify65Api with
    name := Spec.MlDsa.verify65Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verify65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify65With v.callee
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify65_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify87Api with
    name := Spec.MlDsa.verify87Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verify87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify87With v.callee
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify87_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlDsaVerify
