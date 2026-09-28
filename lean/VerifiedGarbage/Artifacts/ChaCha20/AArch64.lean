import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.ChaCha20.AArch64.Shared

/-!
# The ChaCha20 block function (RFC 8439) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := AArch64.target
    doc := Spec.ChaCha20.blockApi.doc ["`buf` must not overlap `state`."]
    code := Impl.ChaCha20.AArch64.block
    contract := Spec.ChaCha20.blockContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.Shared.block
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.AArch64
