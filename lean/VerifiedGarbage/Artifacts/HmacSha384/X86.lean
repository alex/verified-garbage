import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.InitAny

/-!
# HMAC-SHA-384 (RFC 2104) on x86

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
(`Impl/Hmac/Generic/X86.lean`), calling SHA-384's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha384.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.initAnyKeyApi with
    target := X86.target
    doc := Spec.Hmac.sha384I.initAnyKeyApi.doc
    code := sha384H.initAny
    contract := Spec.Hmac.sha384I.initAnyKeyContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initAnyKeyContract; rfl⟩
    stack := 48
    verified := Instances.sha384_initAny
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha384I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Instances.sha384_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha384.X86
