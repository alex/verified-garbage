import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20.X86_64.Shared
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# The ChaCha20 block function (RFC 8439) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86_64.target
    doc := Spec.ChaCha20.blockApi.doc ["`buf` must not overlap `state`, nor the return address on \
      the stack (distinct Rust objects never do)."]
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.Shared.block },
  { Spec.ChaCha20.xorApi with
    target := X86_64.target
    doc := Spec.ChaCha20.xorApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its calls of \
      `vg_chacha20_block` store their return address, and none of them may wrap around the end of \
      the address space (distinct Rust objects never do)."]
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    verified := Proof.ChaCha20.X86_64.Shared.xor }]

end VG.Artifacts.ChaCha20.X86_64
