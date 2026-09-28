import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Hmac.X86_64.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Hmac.X86_64

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := X86_64.target
    doc := Spec.Hmac.initSha256Api.doc ["These four regions must not overlap each other, the \
      return address on the stack, or the 8 bytes of stack below it, where its calls of \
      `vg_sha256_compress` store their return address (distinct Rust objects never do)."]
    code := Impl.Hmac.X86_64.init
    contract := Spec.Hmac.initSha256Contract X86_64.abi 8
    verified := Proof.Hmac.X86_64.Shared.init },
  { Spec.Hmac.finalizeSha256Api with
    target := X86_64.target
    doc := Spec.Hmac.finalizeSha256Api.doc ["These three regions must not overlap each other, the \
      return address on the stack, or the 16 bytes of stack below it, where its calls of \
      `vg_sha256_finalize` (which calls `vg_sha256_compress`) store their return addresses \
      (distinct Rust objects never do)."]
    code := Impl.Hmac.X86_64.finalize
    contract := Spec.Hmac.finalizeSha256Contract X86_64.abi 16
    verified := Proof.Hmac.X86_64.Shared.finalize }]

end VG.Artifacts.Hmac.X86_64
