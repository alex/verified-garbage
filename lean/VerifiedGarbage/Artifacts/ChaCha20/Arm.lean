import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20.Arm.Shared

/-!
# The ChaCha20 block function (RFC 8439) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := Arm.target
    doc := Spec.ChaCha20.blockApi.doc ["`buf` must not overlap `state`, and neither may wrap \
      around the end of the address space (no Rust object does)."]
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockContract Arm.abi
    verified := Proof.ChaCha20.Arm.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.Arm
