import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

namespace VG.Generic.MdHash.AArch64.Ed25519PublicKey

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
  { Spec.Ed25519.publicKeyApi with
    name := Spec.Ed25519.publicKeyApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ed25519.publicKeyApi.doc
    code := Impl.Ed25519.AArch64.PublicKey.code v.code v.suffix
    contract := Spec.Ed25519.publicKeyContract AArch64.abi 352
    stack := 352
    verified := Proof.Ed25519.AArch64.PublicKey.publicKey_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519PublicKey
