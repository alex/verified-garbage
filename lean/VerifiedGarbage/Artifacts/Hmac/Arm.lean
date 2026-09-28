import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Arm.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Hmac.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := Arm.target
    doc := Spec.Hmac.initSha256Api.doc ["These four regions must not overlap each other, and \
      `inner`, `outer` and `scratch` must not overlap the call's stack argument; none of them may \
      wrap around the end of the address space (distinct Rust objects never do)."]
    code := Impl.Hmac.Arm.init
    contract := Spec.Hmac.initSha256Contract Arm.abi
    verified := Proof.Hmac.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.finalizeSha256OutApi with
    target := Arm.target
    doc := Spec.Hmac.finalizeSha256OutApi.doc ["`inner`, `out` and `scratch` must not overlap each \
      other, `outer` or the call's stack arguments, and none of the four may wrap around the end \
      of the address space (distinct Rust objects never do)."]
    code := Impl.Hmac.Arm.finalize
    contract := Spec.Hmac.finalizeSha256OutContract Arm.abi
    verified := Proof.Hmac.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Hmac.Arm
