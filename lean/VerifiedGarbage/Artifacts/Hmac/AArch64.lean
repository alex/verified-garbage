import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Hmac.AArch64.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Hmac.AArch64

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := AArch64.target
    doc := Spec.Hmac.initSha256Api.doc ["These four regions must not overlap each other, or the 16 \
      bytes of stack below the stack pointer, where it saves its return address (distinct Rust \
      objects never do)."]
    code := Impl.Hmac.AArch64.init
    contract := Spec.Hmac.initSha256Contract AArch64.abi 16
    verified := Proof.Hmac.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.finalizeSha256Api with
    target := AArch64.target
    doc := Spec.Hmac.finalizeSha256Api.doc ["These three regions must not overlap each other, or \
      the 32 bytes of stack below the stack pointer, where it and its calls of \
      `vg_sha256_finalize` save their return addresses (distinct Rust objects never do)."]
    code := Impl.Hmac.AArch64.finalize
    contract := Spec.Hmac.finalizeSha256Contract AArch64.abi 32
    verified := Proof.Hmac.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Hmac.AArch64
