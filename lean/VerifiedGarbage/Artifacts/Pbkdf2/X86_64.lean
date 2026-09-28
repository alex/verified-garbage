import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Shared

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Pbkdf2.X86_64

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := X86_64.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc ["`t` and `scratch` must not overlap each other, `key` \
      or `u`, and none of the four regions may overlap the return address on the stack or the 8 \
      bytes of stack below it, where its calls of `vg_sha256_compress` store their return address \
      (distinct Rust objects never do)."]
    code := Impl.Pbkdf2.X86_64.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8
    verified := Proof.Pbkdf2.X86_64.Shared.iterate }]

end VG.Artifacts.Pbkdf2.X86_64
