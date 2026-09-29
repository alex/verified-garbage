import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Verified

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20Poly1305.X86

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := X86.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.X86.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20Poly1305.X86.seal_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.ChaCha20Poly1305.openApi with
    target := X86.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.X86.«open»
    contract := Spec.ChaCha20Poly1305.openContract X86.abi 32
    stack := 32
    verified := Proof.ChaCha20Poly1305.X86.open_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.ChaCha20Poly1305.X86
