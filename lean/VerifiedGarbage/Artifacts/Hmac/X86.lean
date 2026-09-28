import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.X86.Shared

/-!
# HMAC-SHA-256 (RFC 2104) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Hmac.X86

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := X86.target
    doc := Spec.Hmac.initSha256Api.doc ["These four regions must not overlap each other or the \
      arguments of the call, `inner`, `outer` and `scratch` must not overlap its return address, \
      and none of them may wrap around the end of the address space (distinct Rust objects never \
      do)."]
      (notes := ["The function overwrites its own arguments on the stack (which the callee owns \
        under cdecl)."])
    code := Impl.Hmac.X86.init
    contract := Spec.Hmac.initSha256Contract X86.abi
    verified := Proof.Hmac.X86.Shared.init },
  { Spec.Hmac.finalizeSha256OutApi with
    target := X86.target
    doc := Spec.Hmac.finalizeSha256OutApi.doc ["`inner`, `out` and `scratch` must not overlap each \
      other, `outer` or the stack frame of the call (the return address and the arguments); \
      `outer` must not overlap the arguments; and none of the four may wrap around the end of the \
      address space (distinct Rust objects never do)."]
      (notes := ["The function overwrites its own arguments on the stack (which the callee owns \
        under cdecl)."])
    code := Impl.Hmac.X86.finalize
    contract := Spec.Hmac.finalizeSha256OutContract X86.abi
    verified := Proof.Hmac.X86.Shared.finalize }]

end VG.Artifacts.Hmac.X86
