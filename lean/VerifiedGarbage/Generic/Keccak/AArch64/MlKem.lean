import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps

/-! `keygen`, `encaps` and `decaps` of ML-KEM-768 and ML-KEM-1024, for each
Keccak implementation: the same code and proofs, for each parameter set. -/

namespace VG.Generic.Keccak.AArch64.MlKem

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlKem.keyGenApi with
    name := Spec.MlKem.keyGenApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.keyGenApi.doc
    code := Impl.MlKem.AArch64.keyGenWith v.callee
    contract := Spec.MlKem.keyGenContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.encapsApi with
    name := Spec.MlKem.encapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.encapsApi.doc
    code := Impl.MlKem.AArch64.encapsWith v.callee
    contract := Spec.MlKem.encapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.Encaps.encaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decapsApi with
    name := Spec.MlKem.decapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.decapsApi.doc
    code := Impl.MlKem.AArch64.decapsWith v.callee
    contract := Spec.MlKem.decapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.Decaps.decaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
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

end VG.Generic.Keccak.AArch64.MlKem
