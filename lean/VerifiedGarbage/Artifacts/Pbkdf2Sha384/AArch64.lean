import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.AArch64.Instances

/-!
# The PBKDF2-HMAC-SHA-384 iteration (RFC 8018) on AArch64

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
(`Impl/Pbkdf2/Generic/AArch64.lean`), calling SHA-384's verified `update` and
`finalize`.
-/

namespace VG.Artifacts.Pbkdf2Sha384.AArch64

open VG.Proof.Hmac.Generic.AArch64

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.iterateApi with
    target := AArch64.target
    doc := Spec.Hmac.sha384I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.AArch64.iterate sha384H
    contract := Spec.Hmac.sha384I.iterateContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.AArch64.Instances.sha384
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Sha384.AArch64
