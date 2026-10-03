import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Lit

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on x86 -/

namespace VG.Artifacts.ChaCha20Poly1305.X86

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := X86.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.X86.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20Poly1305.X86.seal_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.ChaCha20Poly1305.openApi with
    target := X86.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.X86.«open»
    contract := Spec.ChaCha20Poly1305.openContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20Poly1305.X86.open_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.ChaCha20Poly1305.X86
