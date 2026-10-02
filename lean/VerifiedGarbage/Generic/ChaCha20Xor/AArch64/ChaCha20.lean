import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  { Spec.ChaCha20.xorApi with
    name := Spec.ChaCha20.xorApi.name ++ v.callee.suffix
    target := AArch64.target
    doc := Spec.ChaCha20.xorApi.doc (notes := v.notes)
    code := v.callee.code
    contract := Spec.ChaCha20.xorContract AArch64.abi
    verified := v.verified
    features := v.features
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20
