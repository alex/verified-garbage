import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances

/-!
# HMAC-MD5 (RFC 2104) on ARMv7

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
(`Impl/Hmac/Generic/Arm.lean`), calling MD5's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacMd5.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.initApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.initApi.doc
    code := md5H.init
    contract := Spec.Hmac.md5I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.md5_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.finalizeApi.doc
    code := md5H.finalize
    contract := Spec.Hmac.md5I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.md5_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacMd5.Arm
