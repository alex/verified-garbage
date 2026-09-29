import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Pbkdf2.X86
import VerifiedGarbage.Proof.Pbkdf2.X86.Iterate

/-!
# The PBKDF2-HMAC-SHA-256 iteration (RFC 8018) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Pbkdf2Sha256.X86

def artifacts : List Artifact := [
  { Spec.Pbkdf2.iterateSha256Api with
    target := X86.target
    doc := Spec.Pbkdf2.iterateSha256Api.doc
    code := Impl.Pbkdf2.X86.iterate
    contract := Spec.Pbkdf2.iterateSha256Contract X86.abi 20
    stack := 20
    verified := Proof.Pbkdf2.X86.iterate_verified }]

end VG.Artifacts.Pbkdf2Sha256.X86
