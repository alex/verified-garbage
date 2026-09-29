import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Shared

/-!
# SHA-256 (FIPS 180-4) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha256.X86

def artifacts : List Artifact := [
  { Spec.Sha256.compressApi with
    target := X86.target
    doc := Spec.Sha256.compressApi.doc
    code := Impl.Sha256.X86.compress
    contract := Spec.Sha256.compressContract X86.abi
    verified := Proof.Sha256.X86.Shared.compress },
  { Spec.Sha256.initApi with
    target := X86.target
    doc := Spec.Sha256.initApi.doc
    code := Impl.Sha256.X86.Stream.init
    contract := Spec.Sha256.initContract X86.abi
    verified := Proof.Sha256.X86.Shared.init },
  { Spec.Sha256.updateApi with
    target := X86.target
    doc := Spec.Sha256.updateApi.doc
    code := Impl.Sha256.X86.Stream.update
    contract := Spec.Sha256.updateContract X86.abi
    verified := Proof.Sha256.X86.Shared.update },
  { Spec.Sha256.finalizeApi with
    target := X86.target
    doc := Spec.Sha256.finalizeApi.doc
    code := Impl.Sha256.X86.Stream.finalize
    contract := Spec.Sha256.finalizeContract X86.abi
    verified := Proof.Sha256.X86.Shared.finalize }]

end VG.Artifacts.Sha256.X86
