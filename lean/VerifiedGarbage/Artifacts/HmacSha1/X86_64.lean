import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Shared

/-!
# HMAC-SHA-1 (RFC 2104) on x86-64

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
(`Impl/Hmac/Generic/X86_64.lean`), calling SHA-1's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha1.X86_64

open VG.Proof.Hmac.Generic.X86_64

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := sha1H.init
    contract := Spec.Hmac.sha1I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha1_init },
  { Spec.Hmac.sha1I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := sha1H.finalize
    contract := Spec.Hmac.sha1I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha1_finalize }]

end VG.Artifacts.HmacSha1.X86_64
