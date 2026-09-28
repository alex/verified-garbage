import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Pbkdf2.Arm
import VerifiedGarbage.Proof.Pbkdf2.Arm.Shared

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Pbkdf2.Arm

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := Arm.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc ["`t` and `scratch` must not overlap each other, `key` \
      or `u` (distinct Rust objects never do). The function uses no stack: it saves its return \
      address in `scratch`."]
    code := Impl.Pbkdf2.Arm.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract Arm.abi
    verified := Proof.Pbkdf2.Arm.Shared.iterate
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2.Arm
