import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on AArch64

A generic caller (see `TCB/Emit.lean`), emitted for every ChaCha20 stream
backend. The one-time Poly1305 key uses the scalar block function. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract. The functions use no stack: their calls (`bl`) keep
the return address in `x30`, which they save in the context.
-/

namespace VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305

def artifacts (v : Proof.ChaCha20.AArch64.XorImpl) : List Artifact := [
  { Spec.ChaCha20Poly1305.sealApi with
    name := Spec.ChaCha20Poly1305.sealApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.sealApi.doc
    code := Impl.ChaCha20Poly1305.AArch64.sealWith v.callee
    contract := Spec.ChaCha20Poly1305.sealContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.seal_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20Poly1305.openApi with
    name := Spec.ChaCha20Poly1305.openApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.ChaCha20Poly1305.openApi.doc
    code := Impl.ChaCha20Poly1305.AArch64.openWith v.callee
    contract := Spec.ChaCha20Poly1305.openContract AArch64.abi
    verified := Proof.ChaCha20Poly1305.AArch64.open_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.ChaCha20Xor.AArch64.ChaCha20Poly1305
