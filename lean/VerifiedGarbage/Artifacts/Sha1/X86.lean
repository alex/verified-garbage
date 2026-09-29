import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha1.X86.Shared

/-!
# SHA-1 (FIPS 180-4) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha1.X86

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := X86.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.X86.compress
    contract := Spec.Sha1.compressContract X86.abi
    verified := Proof.Sha1.X86.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha1.initApi with
    target := X86.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.X86.Stream.init
    contract := Spec.Sha1.initContract X86.abi
    verified := Proof.Sha1.X86.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha1.updateApi with
    target := X86.target
    doc := Spec.Sha1.updateApi.doc
    code := Impl.Sha1.X86.Stream.update
    contract := Spec.Sha1.updateContract X86.abi 20
    stack := 20
    verified := Proof.Sha1.X86.Shared.update
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha1.finalizeApi with
    target := X86.target
    doc := Spec.Sha1.finalizeApi.doc
    code := Impl.Sha1.X86.Stream.finalize
    contract := Spec.Sha1.finalizeContract X86.abi 20
    stack := 20
    verified := Proof.Sha1.X86.Shared.finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha1.X86
