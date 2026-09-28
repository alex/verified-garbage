import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# SHA-256 (FIPS 180-4) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha256.Arm

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := Arm.target
    doc := Spec.Sha256.compressApi.doc ["These three regions must not overlap each other, and none \
      of them may wrap around the end of the address space (no Rust object does)."]
    code := Impl.Sha256.Arm.compress
    contract := Spec.Sha256.compressContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.initApi with
    target := Arm.target
    doc := Spec.Sha256.initApi.doc ["It must not wrap around the end of the address space (no Rust \
      object does)."]
    code := Impl.Sha256.Arm.Stream.init
    contract := Spec.Sha256.initContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.updateApi with
    target := Arm.target
    doc := Spec.Sha256.updateApi.doc ["These three regions must not overlap each other, nor the \
      arguments passed on the stack, and none of them may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.Sha256.Arm.Stream.update
    contract := Spec.Sha256.updateContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha256.finalizeApi with
    target := Arm.target
    doc := Spec.Sha256.finalizeApi.doc ["These three regions must not overlap each other, nor the \
      arguments passed on the stack, and none of them may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.Sha256.Arm.Stream.finalize
    contract := Spec.Sha256.finalizeContract Arm.abi
    verified := Proof.Sha256.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha256.Arm
