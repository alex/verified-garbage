import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.X86_64.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := X86_64.target
    doc := Spec.Poly1305.initApi.doc ["`state` must not overlap `key` or the return address on the \
      stack (distinct Rust objects never do)."]
    code := Impl.Poly1305.X86_64.init
    contract := Spec.Poly1305.initContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.init },
  { Spec.Poly1305.blocksApi with
    target := X86_64.target
    doc := Spec.Poly1305.blocksApi.doc ["`state` must not overlap `blocks` or the return address on \
      the stack, and `blocks` must not wrap around the end of the address space (distinct Rust \
      objects never do)."]
    code := Impl.Poly1305.X86_64.blocks
    contract := Spec.Poly1305.blocksContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.blocks },
  { Spec.Poly1305.finalizeTailApi with
    target := X86_64.target
    doc := Spec.Poly1305.finalizeTailApi.doc ["These three regions must not overlap each other or the \
      return address on the stack (distinct Rust objects never do)."]
    code := Impl.Poly1305.X86_64.finalize
    contract := Spec.Poly1305.finalizeTailContract X86_64.abi
    verified := Proof.Poly1305.X86_64.Shared.finalize }]

end VG.Artifacts.Poly1305.X86_64
