import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.Instances

/-!
# The PBKDF2-HMAC-SHA-512 iteration (RFC 8018) on x86

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
(`Impl/Pbkdf2/Generic/X86.lean`), calling SHA-512's verified `update` and
`finalize`.
-/

namespace VG.Artifacts.Pbkdf2Sha512.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha512I.iterateApi with
    target := X86.target
    doc := Spec.Hmac.sha512I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86.iterate sha512H'
    contract := Spec.Hmac.sha512I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 48
    verified := Proof.Pbkdf2.Generic.X86.Instances.sha512
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Pbkdf2Sha512.X86
