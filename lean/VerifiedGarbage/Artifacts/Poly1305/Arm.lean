import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Poly1305.Arm.Init
import VerifiedGarbage.Proof.Poly1305.Arm.Update
import VerifiedGarbage.Proof.Poly1305.Arm.Finalize

/-!
# Poly1305 (RFC 8439 §2.5) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Poly1305.Arm

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := Arm.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.Arm.init
    contract := Spec.Poly1305.initContract Arm.abi
    verified := Proof.Poly1305.Arm.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.blocksApi with
    target := Arm.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.Arm.blocks
    contract := Spec.Poly1305.blocksContract Arm.abi
    verified := Proof.Poly1305.Arm.blocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.updateApi with
    target := Arm.target
    doc := Spec.Poly1305.updateApi.doc
    code := Impl.Poly1305.Arm.update
    contract := Spec.Poly1305.updateContract Arm.abi
    verified := Proof.Poly1305.Arm.Update.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.finalizeApi with
    target := Arm.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.Arm.finalize
    contract := Spec.Poly1305.finalizeContract Arm.abi
    verified := Proof.Poly1305.Arm.Fin.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Poly1305.Arm
