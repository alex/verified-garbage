import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze

/-!
# SHA-3 and SHAKE (FIPS 202) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha3.AArch64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := AArch64.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.AArch64.permute
    contract := Spec.Sha3.permuteContract AArch64.abi
    verified := Proof.Sha3.AArch64.permute_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.absorbApi with
    target := AArch64.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.Sha3.AArch64.Stream.absorb
    contract := Spec.Sha3.absorbContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha3.AArch64.Stream.Absorb.absorb_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    target := AArch64.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.Sha3.AArch64.Stream.pad
    contract := Spec.Sha3.padContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha3.AArch64.Stream.Pad.pad_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    target := AArch64.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.Sha3.AArch64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha3.AArch64.Stream.Squeeze.squeeze_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha3.AArch64
