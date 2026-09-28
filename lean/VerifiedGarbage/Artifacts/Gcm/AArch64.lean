import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Gcm.AArch64.Shared

/-!
# GHASH on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := AArch64.target
    doc := Spec.Gcm.ghashApi.doc ["`y` and `scratch` must not overlap each other, `h` or `data` \
      (`h` and `data` may overlap), and none of the four regions may wrap around the end of the \
      address space (distinct Rust objects never do)."]
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.AArch64.ghash
    contract := Spec.Gcm.ghashContract AArch64.abi
    verified := Proof.Gcm.AArch64.Shared.ghash
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gcm.AArch64
