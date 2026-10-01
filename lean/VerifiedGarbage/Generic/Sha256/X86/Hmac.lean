import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-! Generic hmac registrations for every x86 SHA-256 backend. -/

namespace VG.Generic.Sha256.X86.Hmac

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.initSha256Api with
    name := Spec.Hmac.initSha256Api.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.initSha256Api.doc
    code := Impl.Hmac.Sha256.X86.init v.cmpN v.cmpC
    contract := Spec.Hmac.initSha256Contract X86.abi 20
    stack := 20
    verified := Proof.Hmac.Sha256.X86.Init.verified v.cmp v.cmpSp v.cmpStack v.initCt
    spSafe := v.initSp
    features := v.features },
  { Spec.Hmac.finalizeSha256OutApi with
    name := Spec.Hmac.finalizeSha256OutApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.finalizeSha256OutApi.doc
    code := Impl.Hmac.Sha256.X86.finalize v.cmpN v.cmpC
    contract := Spec.Hmac.finalizeSha256OutContract X86.abi 20
    stack := 20
    verified := Proof.Hmac.Sha256.X86.Finalize.verified v.cmp v.cmpSp v.cmpStack v.finHashSp v.finHashStack v.finCt
    spSafe := v.finSp
    features := v.features }]

end VG.Generic.Sha256.X86.Hmac
