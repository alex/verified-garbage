import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256

/-!
Generic PBKDF2 registrations for every x86 SHA-256 backend: the iteration,
and the whole derivation (`Impl/Pbkdf2/Whole/X86.lean`), which calls the
backend's streaming, HMAC and PBKDF2 functions (`Proof.Pbkdf2.Whole.X86.sha256Fns`).
`stack` is that of the shared contracts: 76 bytes for `pbkdf2`, which pushes
up to 24 bytes of arguments for the functions it calls, and their return
address, and gives them 48.
-/
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
    features := v.features },
  { Spec.Hmac.sha256I.pbkdf2Api with
    name := Spec.Hmac.sha256I.pbkdf2Api.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.pbkdf2Api.doc
    code := (Proof.Pbkdf2.Whole.X86.sha256FnsOf v).pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.sha256_verified v
    spSafe := v.pbkdf2Sp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2
