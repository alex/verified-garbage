import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances

/-!
# HMAC-SHA-512/256 (RFC 2104) on x86

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
(`Impl/Hmac/Generic/X86.lean`), calling SHA-512/256's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha512_256.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := sha512_256H.init
    contract := Spec.Hmac.sha512_256I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Instances.sha512_256_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := sha512_256H.finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Instances.sha512_256_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha512_256.X86
