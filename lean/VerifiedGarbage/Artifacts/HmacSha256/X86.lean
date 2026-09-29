import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.X86.Init

/-!
# HMAC-SHA-256 (RFC 2104) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.HmacSha256.X86

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := X86.target
    doc := Spec.Hmac.initSha256Api.doc
    code := Impl.Hmac.X86.init
    contract := Spec.Hmac.initSha256Contract X86.abi 20
    stack := 20
    verified := Proof.Hmac.X86.Init.init_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Hmac.finalizeSha256OutApi with
    target := X86.target
    doc := Spec.Hmac.finalizeSha256OutApi.doc
    code := Impl.Hmac.X86.finalize
    contract := Spec.Hmac.finalizeSha256OutContract X86.abi 20
    stack := 20
    verified := Proof.Hmac.X86.Finalize.finalize_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.HmacSha256.X86
