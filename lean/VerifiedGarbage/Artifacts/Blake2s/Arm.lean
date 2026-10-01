import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Blake2.Arm.Blake2s

/-!
# BLAKE2s (RFC 7693) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Blake2s.Arm

def artifacts : List Artifact := [
  { Spec.Blake2.compressSApi with
    target := Arm.target
    doc := Spec.Blake2.compressSApi.doc
    code := Impl.Blake2.Arm.S.compress
    contract := Spec.Blake2.compressSContract Arm.abi
    verified := Proof.Blake2.ArmS.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.initSApi with
    target := Arm.target
    doc := Spec.Blake2.initSApi.doc
    code := Impl.Blake2.Arm.Stream.init Spec.Blake2.s
    contract := Spec.Blake2.initSContract Arm.abi
    verified := Proof.Blake2.Arm.Blake2s.initS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.updateSApi with
    target := Arm.target
    doc := Spec.Blake2.updateSApi.doc
    code := Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress
    contract := Spec.Blake2.updateSContract Arm.abi 16
    stack := 16
    verified := Proof.Blake2.Arm.Blake2s.updateS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.finalizeSApi with
    target := Arm.target
    doc := Spec.Blake2.finalizeSApi.doc
    code := Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress
    contract := Spec.Blake2.finalizeSContract Arm.abi 16
    stack := 16
    verified := Proof.Blake2.Arm.Blake2s.finalizeS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blake2s.Arm
