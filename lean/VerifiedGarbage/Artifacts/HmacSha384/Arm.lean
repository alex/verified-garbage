import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.InitAny

/-!
# HMAC-SHA-384 (RFC 2104) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-384's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha384.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.initAnyKeyApi with
    target := Arm.target
    doc := Spec.Hmac.sha384I.initAnyKeyApi.doc
    code := sha384H.initAny
    contract := Spec.Hmac.sha384I.initAnyKeyContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initAnyKeyContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_initAny
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha384I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha384.Arm
