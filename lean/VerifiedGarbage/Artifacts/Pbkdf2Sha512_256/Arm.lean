import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.Arm.Instances

/-!
# The PBKDF2-HMAC-SHA-512/256 iteration (RFC 8018) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The code is the one PBKDF2 iteration for every streaming hash function
(`Impl/Pbkdf2/Generic/Arm.lean`), calling SHA-512/256's verified `update` and
`finalize`.
-/

namespace VG.Artifacts.Pbkdf2Sha512_256.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.iterateApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_256I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.Arm.iterate sha512_256H
    contract := Spec.Hmac.sha512_256I.iterateContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Generic.Arm.Instances.sha512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha512_256.Arm
