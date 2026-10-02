import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# HMAC-SHA-1 (RFC 2104) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

`init` is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86.lean`), calling SHA-1's verified `init` and `update`.
`finalize` is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): it calls SHA-1's verified streaming `finalize`
for the inner hash, then computes the outer hash with one call of SHA-1's
verified compression function, on a block it lays out word by word in
`scratch`: the outer key's hash value, the inner digest, its padding and
length.
-/

namespace VG.Artifacts.HmacSha1.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := sha1H.init
    contract := Spec.Hmac.sha1I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Instances.sha1_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := Proof.Pbkdf2.Md.X86.sha1M.hmacFin
    contract := Spec.Hmac.sha1I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha1_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha1.X86
