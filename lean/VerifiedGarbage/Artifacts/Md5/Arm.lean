import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Md5.Arm.Shared

/-!
# MD5 (RFC 1321) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Md5.Arm

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := Arm.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.Arm.compress
    contract := Spec.Md5.compressContract Arm.abi
    verified := Proof.Md5.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.initApi with
    target := Arm.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.Arm.Stream.init
    contract := Spec.Md5.initContract Arm.abi
    verified := Proof.Md5.Arm.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.updateApi with
    target := Arm.target
    doc := Spec.Md5.updateApi.doc
    code := Impl.Md5.Arm.Stream.update
    contract := Spec.Md5.updateContract Arm.abi
    verified := Proof.Md5.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Md5.finalizeApi with
    target := Arm.target
    doc := Spec.Md5.finalizeApi.doc
    code := Impl.Md5.Arm.Stream.finalize
    contract := Spec.Md5.finalizeContract Arm.abi
    verified := Proof.Md5.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Md5.Arm
