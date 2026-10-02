import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT

/-!
# The ChaCha20 block function (RFC 8439) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := Arm.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.Arm.block
    contract := Spec.ChaCha20.blockContract Arm.abi
    verified := Proof.ChaCha20.Arm.block_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.xorApi with
    target := Arm.target
    doc := Spec.ChaCha20.xorApi.doc
    code := Impl.ChaCha20.Arm.Xor.xor
    contract := Spec.ChaCha20.xorContract Arm.abi
    verified := Proof.ChaCha20.Arm.Xor.xor_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.initApi with
    target := Arm.target
    doc := Spec.ChaCha20.initApi.doc
    code := Impl.ChaCha20.Arm.Stream.init
    contract := Spec.ChaCha20.initContract Arm.abi
    verified := Proof.ChaCha20.Arm.Stream.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.setNonceApi with
    target := Arm.target
    doc := Spec.ChaCha20.setNonceApi.doc
    code := Impl.ChaCha20.Arm.Stream.setNonce
    contract := Spec.ChaCha20.setNonceContract Arm.abi
    verified := Proof.ChaCha20.Arm.Stream.setNonce_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.ChaCha20.applyApi with
    target := Arm.target
    doc := Spec.ChaCha20.applyApi.doc
    code := Impl.ChaCha20.Arm.Stream.apply
    contract := Spec.ChaCha20.applyContract Arm.abi 0
    verified := Proof.ChaCha20.Arm.Stream.apply_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.Arm
