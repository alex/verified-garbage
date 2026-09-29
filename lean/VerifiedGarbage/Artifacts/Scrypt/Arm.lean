import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Scrypt.Arm.Salsa
import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix
import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Salsa

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := Arm.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.Arm.salsa
    contract := Spec.Scrypt.salsaContract Arm.abi
    verified := Proof.Scrypt.Arm.salsa_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.blockMixApi with
    target := Arm.target
    doc := Spec.Scrypt.blockMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.blockMix
    contract := Spec.Scrypt.blockMixContract Arm.abi
    verified := Proof.Scrypt.Arm.BlockMix.blockMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.roMixApi with
    target := Arm.target
    doc := Spec.Scrypt.roMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.roMix
    contract := Spec.Scrypt.roMixContract Arm.abi
    verified := Proof.Scrypt.Arm.RoMix.roMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Scrypt.Arm
