import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha1.X86_64.Shared

/-!
# SHA-1 (FIPS 180-4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha1.X86_64

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := X86_64.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.X86_64.compress
    contract := Spec.Sha1.compressContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.compress },
  { Spec.Sha1.initApi with
    target := X86_64.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.X86_64.Stream.init
    contract := Spec.Sha1.initContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.init },
  { Spec.Sha1.updateApi with
    target := X86_64.target
    doc := Spec.Sha1.updateApi.doc
    code := Impl.Sha1.X86_64.Stream.update
    contract := Spec.Sha1.updateContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha1.X86_64.Shared.update },
  { Spec.Sha1.finalizeApi with
    target := X86_64.target
    doc := Spec.Sha1.finalizeApi.doc
    code := Impl.Sha1.X86_64.Stream.finalize
    contract := Spec.Sha1.finalizeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha1.X86_64.Shared.finalize }]

end VG.Artifacts.Sha1.X86_64
