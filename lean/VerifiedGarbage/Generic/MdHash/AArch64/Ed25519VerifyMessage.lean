import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-! Whole-message Ed25519 verification follows every SHA-512 backend carried
by MdHash. The signature and contract come from the reviewed Ed25519 API. -/
namespace VG.Generic.MdHash.AArch64.Ed25519VerifyMessage

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
    { Spec.Ed25519.verifyApi with
      name := Spec.Ed25519.verifyApi.name ++ v.suffix
      target := AArch64.target
      doc := Spec.Ed25519.verifyApi.doc (notes := ["Hashes R, the public key and the message with \
        the selected SHA-512 backend, reduces the challenge modulo L, and checks the signature \
        equation. The 336-byte stack frame holds the digest, challenge, saved arguments and return address; \
        the SHA-512 calls use another 16 bytes below it."])
      code := Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix
      contract := Spec.Ed25519.verifyContract AArch64.abi 352
      stack := 352
      verified := Proof.Ed25519.AArch64.VerifyMessage.verifyMessage_verified v
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519VerifyMessage
