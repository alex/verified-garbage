import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps

namespace VG.Generic.Keccak.AArch64.MlKem1024

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlKem1024.keyGenApi with
    name := Spec.MlKem1024.keyGenApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.keyGenApi.doc
    code := Impl.MlKem1024.AArch64.keyGenWith v.callee
    contract := Spec.MlKem1024.keyGenContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.encapsApi with
    name := Spec.MlKem1024.encapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.encapsApi.doc
    code := Impl.MlKem1024.AArch64.encapsWith v.callee
    contract := Spec.MlKem1024.encapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.Encaps.encaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decapsApi with
    name := Spec.MlKem1024.decapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.decapsApi.doc
    code := Impl.MlKem1024.AArch64.decapsWith v.callee
    contract := Spec.MlKem1024.decapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.Decaps.decaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlKem1024
