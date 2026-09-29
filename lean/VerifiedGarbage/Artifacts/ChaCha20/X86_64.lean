import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# The ChaCha20 block function (RFC 8439) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.ChaCha20.X86_64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := X86_64.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.X86_64.block
    contract := Spec.ChaCha20.blockContract X86_64.abi
    verified := Proof.ChaCha20.X86_64.block_verified },
  { Spec.ChaCha20.xorApi with
    target := X86_64.target
    doc := Spec.ChaCha20.xorApi.doc
    code := Impl.ChaCha20.X86_64.Xor.xor
    contract := Spec.ChaCha20.xorContract X86_64.abi 8
    stack := 8
    verified := Proof.ChaCha20.X86_64.Xor.xor_verified }]

end VG.Artifacts.ChaCha20.X86_64
