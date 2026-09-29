import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Shared

/-!
# HMAC (RFC 2104) over the streaming hash functions on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.

One implementation serves every hash function: it calls the hash's own
verified `init`, `update` and `finalize` (see
`Impl/Hmac/Generic/X86_64.lean`).
-/

namespace VG.Artifacts.Hmac.Generic.X86_64

open VG.Proof.Hmac.Generic.X86_64

/-- What the regions must not overlap, on x86-64. -/
def overlap : List String := ["These four regions must not overlap each other, the return address on \
  the stack, or the 16 bytes of stack below it, where its calls, and theirs, store their return \
  addresses (distinct Rust objects never do)."]

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha1I.initApi.doc overlap
    code := sha1H.init
    contract := Spec.Hmac.sha1I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.sha1_init },
  { Spec.Hmac.sha1I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc overlap
    code := sha1H.finalize
    contract := Spec.Hmac.sha1I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.sha1_finalize },
  { Spec.Hmac.md5I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.initApi.doc overlap
    code := md5H.init
    contract := Spec.Hmac.md5I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.md5_init },
  { Spec.Hmac.md5I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.md5I.finalizeApi.doc overlap
    code := md5H.finalize
    contract := Spec.Hmac.md5I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.md5_finalize },
  { Spec.Hmac.sha384I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha384I.initApi.doc overlap
    code := sha384H.init
    contract := Spec.Hmac.sha384I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.sha384_init },
  { Spec.Hmac.sha384I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc overlap
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.sha384_finalize },
  { Spec.Hmac.sha512I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512I.initApi.doc overlap
    code := sha512H'.init
    contract := Spec.Hmac.sha512I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_init },
  { Spec.Hmac.sha512I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512I.finalizeApi.doc overlap
    code := sha512H'.finalize
    contract := Spec.Hmac.sha512I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_finalize },
  { Spec.Hmac.sha512_224I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.initApi.doc overlap
    code := sha512_224H.init
    contract := Spec.Hmac.sha512_224I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_224_init },
  { Spec.Hmac.sha512_224I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_224I.finalizeApi.doc overlap
    code := sha512_224H.finalize
    contract := Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_224_finalize },
  { Spec.Hmac.sha512_256I.initApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.initApi.doc overlap
    code := sha512_256H.init
    contract := Spec.Hmac.sha512_256I.initContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_256_init },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86_64.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc overlap
    code := sha512_256H.finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16
    stack := 16
    verified := Shared.sha512_256_finalize }]

end VG.Artifacts.Hmac.Generic.X86_64
