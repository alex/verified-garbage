import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances

/-!
# PBKDF2-HMAC-MD5 (RFC 8018) on x86: the iteration and the whole derivation

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
(`Impl/Pbkdf2/Generic/X86.lean`), calling MD5's verified `update` and
`finalize`.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contracts: 48 bytes for the iteration, and 76 for
`pbkdf2`, which pushes up to 24 bytes of arguments for the functions it
calls, and their return address.
-/

namespace VG.Artifacts.Pbkdf2Md5.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.iterateApi with
    target := X86.target
    doc := Spec.Hmac.md5I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86.iterate md5H
    contract := Spec.Hmac.md5I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Generic.X86.Instances.md5
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.md5I.pbkdf2Api with
    target := X86.target
    doc := Spec.Hmac.md5I.pbkdf2Api.doc
    code := Proof.Pbkdf2.Whole.X86.md5F.pbkdf2
    contract := Spec.Hmac.md5I.pbkdf2Contract X86.abi 76
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    writeArgs := true
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.md5
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Pbkdf2Md5.X86
