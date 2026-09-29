import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances

/-!
# HMAC-SHA-512/224 (RFC 2104) on AArch64

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
(`Impl/Hmac/Generic/AArch64.lean`), calling SHA-512/224's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha512_224.AArch64

open VG.Proof.Hmac.Generic.AArch64

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_224I.initApi with
    target := AArch64.target
    doc := Spec.Hmac.sha512_224I.initApi.doc
    code := sha512_224H.init
    contract := Spec.Hmac.sha512_224I.initContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_224_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_224I.finalizeApi with
    target := AArch64.target
    doc := Spec.Hmac.sha512_224I.finalizeApi.doc
    code := sha512_224H.finalize
    contract := Spec.Hmac.sha512_224I.finalizeContract AArch64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha512_224_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha512_224.AArch64
