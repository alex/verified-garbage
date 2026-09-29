import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlKem.Arm.Add

/-!
# ML-KEM (FIPS 203) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem.Arm

def artifacts : List Artifact := [
  { Spec.MlKem.addApi with
    target := Arm.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.Arm.add
    contract := Spec.MlKem.addContract Arm.abi
    verified := Proof.MlKem.Arm.Add.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.subApi with
    target := Arm.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.Arm.sub
    contract := Spec.MlKem.subContract Arm.abi
    verified := Proof.MlKem.Arm.Add.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlKem.Arm
