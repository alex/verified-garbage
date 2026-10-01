import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-! Generic PBKDF2 iteration registration for every x86 SHA-256 backend. -/
namespace VG.Generic.Sha256.X86.Pbkdf2

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    name := Spec.Pbkdf2.iterateSha256Api.name ++ v.suffix
    target := X86.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc
    code := Impl.Pbkdf2.Sha256.X86.iterate v.cmpN v.cmpC
    contract := Spec.Pbkdf2.iterateSha256Contract X86.abi 20
    writeArgs := true
    stack := 20
    verified := Proof.Pbkdf2.Sha256.X86.verified v.cmp v.cmpSp v.cmpStack v.iterCt
    spSafe := v.iterSp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2
