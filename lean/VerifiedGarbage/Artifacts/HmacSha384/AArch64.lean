import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances

/-!
# HMAC-SHA-384 (RFC 2104) on AArch64

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
(`Impl/Hmac/Generic/AArch64.lean`), calling SHA-384's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha384.AArch64

open VG.Proof.Hmac.Generic.AArch64

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.initApi with
    target := AArch64.target
    doc := Spec.Hmac.sha384I.initApi.doc
    code := sha384H.init
    contract := Spec.Hmac.sha384I.initContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_init },
  { Spec.Hmac.sha384I.finalizeApi with
    target := AArch64.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha384_finalize }]

end VG.Artifacts.HmacSha384.AArch64
