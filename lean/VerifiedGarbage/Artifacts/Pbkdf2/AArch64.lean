import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Pbkdf2.AArch64
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Shared

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Pbkdf2.AArch64

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := AArch64.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc ["`t` and `scratch` must not overlap each other, `key` \
      or `u` (distinct Rust objects never do). The function uses no stack: it saves its return \
      address in `scratch`."]
    code := Impl.Pbkdf2.AArch64.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract AArch64.abi
    verified := Proof.Pbkdf2.AArch64.Shared.iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2.AArch64
