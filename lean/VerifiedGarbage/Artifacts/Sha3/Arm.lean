import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha3.Arm.Shared

/-!
# SHA-3 and SHAKE (FIPS 202) on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := Arm.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.Arm.permute
    contract := Spec.Sha3.permuteContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.permute
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.absorbApi with
    target := Arm.target
    doc := Spec.Sha3.absorbApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.absorb
    contract := Spec.Sha3.absorbContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.absorb
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    target := Arm.target
    doc := Spec.Sha3.padApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.pad
    contract := Spec.Sha3.padContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.pad
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    target := Arm.target
    doc := Spec.Sha3.squeezeApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.squeeze
    contract := Spec.Sha3.squeezeContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.squeeze
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha3.Arm
