import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.ChaCha20Poly1305.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc ["`ctx` and `data` must not overlap each other, `aad`, the return address on the stack, or the \
      16 bytes of stack below it, where its calls store their return addresses; nor may `aad`. None \
      of them may wrap around the end of the address space (distinct Rust objects never do)."]
    code := Impl.ChaCha20Poly1305.X86_64.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract X86_64.abi 16
    verified := Proof.ChaCha20Poly1305.X86_64.Shared.«seal» },
  { Spec.ChaCha20Poly1305.openApi with
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc ["`ctx` and `data` must not overlap each other, `aad`, the return address on the stack, or the \
      16 bytes of stack below it, where its calls store their return addresses; nor may `aad`. None \
      of them may wrap around the end of the address space (distinct Rust objects never do)."]
    code := Impl.ChaCha20Poly1305.X86_64.«open»
    contract := Spec.ChaCha20Poly1305.openContract X86_64.abi 16
    verified := Proof.ChaCha20Poly1305.X86_64.Shared.«open» }]

end VG.Artifacts.ChaCha20Poly1305.X86_64
