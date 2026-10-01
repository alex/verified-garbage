import VerifiedGarbage.Proof.MlKem.AArch64.Sample

namespace VG.Generic.Keccak.AArch64.MlKemSample

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlKem.sampleNTTApi with
    name := Spec.MlKem.sampleNTTApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.sampleNTTApi.doc
    code := Impl.MlKem.AArch64.sampleNTTWith v.callee
    contract := Spec.MlKem.sampleNTTContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.Sample.sample_verifiedWith v
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlKemSample
