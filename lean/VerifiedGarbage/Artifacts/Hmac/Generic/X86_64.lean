import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Shared

/-!
# HMAC (RFC 2104) over the streaming hash functions on x86-64

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
`Impl/Hmac/Generic/X86_64.lean`).
-/

namespace VG.Artifacts.Hmac.Generic.X86_64

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
    verified := Shared.sha1_finalize },
  { Spec.Hmac.md5I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.initApi.doc
    code := md5H.init
    contract := Spec.Hmac.md5I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.md5_init },
  { Spec.Hmac.md5I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.finalizeApi.doc
    code := md5H.finalize
    contract := Spec.Hmac.md5I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.md5_finalize },
  { Spec.Hmac.sha384I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha384I.initApi.doc
    code := sha384H.init
    contract := Spec.Hmac.sha384I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha384_init },
  { Spec.Hmac.sha384I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha384_finalize },
  { Spec.Hmac.sha512I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512I.initApi.doc
    code := sha512H'.init
    contract := Spec.Hmac.sha512I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_init },
  { Spec.Hmac.sha512I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512I.finalizeApi.doc
    code := sha512H'.finalize
    contract := Spec.Hmac.sha512I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_finalize },
  { Spec.Hmac.sha512_224I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.initApi.doc
    code := sha512_224H.init
    contract := Spec.Hmac.sha512_224I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_224_init },
  { Spec.Hmac.sha512_224I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.finalizeApi.doc
    code := sha512_224H.finalize
    contract := Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_224_finalize },
  { Spec.Hmac.sha512_256I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := sha512_256H.init
    contract := Spec.Hmac.sha512_256I.initContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_256_init },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := sha512_256H.finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Shared.sha512_256_finalize }]

end VG.Artifacts.Hmac.Generic.X86_64
