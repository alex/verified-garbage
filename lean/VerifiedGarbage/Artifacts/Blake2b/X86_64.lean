import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified

/-!
# BLAKE2b (RFC 7693) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Blake2b.X86_64

def artifacts : List Artifact := [
  { Spec.Blake2.compressBApi with
    target := X86_64.target
    doc := Spec.Blake2.compressBApi.doc
    code := Impl.Blake2.X86_64.compress Spec.Blake2.b
    contract := Spec.Blake2.compressBContract X86_64.abi
    verified := Proof.Blake2.X86_64.compressB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.initBApi with
    target := X86_64.target
    doc := Spec.Blake2.initBApi.doc
    code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
    contract := Spec.Blake2.initBContract X86_64.abi
    verified := Proof.Blake2.X86_64.Stream.initB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.updateBApi with
    target := X86_64.target
    doc := Spec.Blake2.updateBApi.doc
    code := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b
    contract := Spec.Blake2.updateBContract X86_64.abi 8
    stack := 8
    verified := Proof.Blake2.X86_64.Stream.updateB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blake2.finalizeBApi with
    target := X86_64.target
    doc := Spec.Blake2.finalizeBApi.doc
    code := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b
    contract := Spec.Blake2.finalizeBContract X86_64.abi 8
    stack := 8
    verified := Proof.Blake2.X86_64.Stream.finalizeB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2b.X86_64
