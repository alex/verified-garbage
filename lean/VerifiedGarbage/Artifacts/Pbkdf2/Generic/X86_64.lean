import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86_64.Shared

/-!
# The PBKDF2-HMAC iteration (RFC 8018) over the streaming hash functions on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract (after unfolding the `Instance`'s contract to the
generic one, which is a `Sig.contract`).

One implementation serves every hash function: it calls the hash's own
verified `init`, `update` and `finalize` (see
`Impl/Pbkdf2/Generic/X86_64.lean`).
-/

namespace VG.Artifacts.Pbkdf2.Generic.X86_64

open VG.Proof.Hmac.Generic.X86_64

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.sha1I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate sha1H
    contract := Spec.Hmac.sha1I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.sha1 },
  { Spec.Hmac.md5I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate md5H
    contract := Spec.Hmac.md5I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.md5 },
  { Spec.Hmac.sha384I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.sha384I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate sha384H
    contract := Spec.Hmac.sha384I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.sha384 },
  { Spec.Hmac.sha512I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate sha512H'
    contract := Spec.Hmac.sha512I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.sha512 },
  { Spec.Hmac.sha512_224I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate sha512_224H
    contract := Spec.Hmac.sha512_224I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.sha512_224 },
  { Spec.Hmac.sha512_256I.iterateApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86_64.iterate sha512_256H
    contract := Spec.Hmac.sha512_256I.iterateContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Generic.X86_64.Shared.sha512_256 }]

end VG.Artifacts.Pbkdf2.Generic.X86_64
