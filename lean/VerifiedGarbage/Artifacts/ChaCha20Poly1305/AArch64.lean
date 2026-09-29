import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract. The functions use no stack: their calls (`bl`) keep
the return address in `x30`, which they save in the context.
-/

namespace VG.Artifacts.ChaCha20Poly1305.AArch64

def artifacts : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.AArch64.«seal»
    contract := Spec.ChaCha20Poly1305.sealContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.seal_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20Poly1305.openApi with
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.AArch64.«open»
    contract := Spec.ChaCha20Poly1305.openContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.open_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20Poly1305.AArch64
