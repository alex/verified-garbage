import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20.X86.Shared

/-!
# The ChaCha20 block function (RFC 8439) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.ChaCha20.X86

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86.target
    doc := Spec.ChaCha20.blockApi.doc ["`buf` must not overlap `state`, the arguments or the \
      return address on the stack, and nothing may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.ChaCha20.X86.block
    contract := Spec.ChaCha20.blockContract X86.abi
    verified := Proof.ChaCha20.X86.Shared.block }]

end VG.Artifacts.ChaCha20.X86
