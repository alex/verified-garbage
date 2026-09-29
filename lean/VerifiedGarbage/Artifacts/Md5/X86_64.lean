import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Md5.X86_64.Shared

/-!
# MD5 (RFC 1321) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := X86_64.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.X86_64.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Md5.initApi with
    target := X86_64.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.X86_64.Stream.init
    contract := Spec.Md5.initContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Md5.updateApi with
    target := X86_64.target
    doc := Spec.Md5.updateApi.doc
    code := Impl.Md5.X86_64.Stream.update
    contract := Spec.Md5.updateContract X86_64.abi 8
    stack := 8
    verified := Proof.Md5.X86_64.Shared.update
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Md5.finalizeApi with
    target := X86_64.target
    doc := Spec.Md5.finalizeApi.doc
    code := Impl.Md5.X86_64.Stream.finalize
    contract := Spec.Md5.finalizeContract X86_64.abi 8
    stack := 8
    verified := Proof.Md5.X86_64.Shared.finalize
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Md5.X86_64
