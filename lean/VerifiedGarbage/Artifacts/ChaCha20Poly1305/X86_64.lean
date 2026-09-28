import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20Poly1305.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.X86_64.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20Poly1305.X86_64.Shared.«seal» },
  { Spec.ChaCha20Poly1305.openApi with
    target := X86_64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.X86_64.«open»
    contract := Spec.ChaCha20Poly1305.openContract X86_64.abi 16
    writeArgs := true
    stack := 16
    verified := Proof.ChaCha20Poly1305.X86_64.Shared.«open» }]

end VG.Artifacts.ChaCha20Poly1305.X86_64
