import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

namespace VG.Generic.ChaCha20Block.AArch64.ChaCha20

def artifacts (v : Proof.ChaCha20.AArch64.BlockImpl) : List Artifact := [
  { Spec.ChaCha20.xorApi with
    name := Spec.ChaCha20.xorApi.name ++ v.callee.suffix
    target := AArch64.target
    doc := Spec.ChaCha20.xorApi.doc (notes := ["Calls `" ++ v.callee.name ++ "`."])
    code := Impl.ChaCha20.AArch64.Xor.xorWith v.callee
    contract := Spec.ChaCha20.xorContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.Xor.xor_verified v
    features := v.features
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.ChaCha20Block.AArch64.ChaCha20
