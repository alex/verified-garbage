import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Shared

/-!
# Poly1305 (RFC 8439 §2.5) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Poly1305.X86

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := X86.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.X86.init
    contract := Spec.Poly1305.initContract X86.abi
    verified := Proof.Poly1305.X86.Shared.init },
  { Spec.Poly1305.blocksApi with
    target := X86.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.X86.blocks
    contract := Spec.Poly1305.blocksContract X86.abi
    verified := Proof.Poly1305.X86.Shared.blocks },
  { Spec.Poly1305.updateApi with
    target := X86.target
    doc := Spec.Poly1305.updateApi.doc
    code := Impl.Poly1305.X86.update
    contract := Spec.Poly1305.updateContract X86.abi
    verified := Proof.Poly1305.X86.Shared.update },
  { Spec.Poly1305.finalizeApi with
    target := X86.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.X86.finalize
    contract := Spec.Poly1305.finalizeContract X86.abi
    verified := Proof.Poly1305.X86.Shared.finalize }]

end VG.Artifacts.Poly1305.X86
