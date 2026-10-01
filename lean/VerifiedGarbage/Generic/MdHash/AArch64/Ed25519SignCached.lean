import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

namespace VG.Generic.MdHash.AArch64.Ed25519SignCached

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
  { Spec.Ed25519.signCachedApi with
    name := Spec.Ed25519.signCachedApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Ed25519.signCachedApi.doc
    code := Impl.Ed25519.AArch64.SignCached.code v.code v.suffix
    contract := Spec.Ed25519.signCachedContract AArch64.abi 336
    stack := 336
    verified := Proof.Ed25519.AArch64.SignCached.signCached_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519SignCached
