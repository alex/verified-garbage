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
    verified := Proof.Sha1.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sha1.initApi with
    target := X86_64.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.X86_64.Stream.init
    contract := Spec.Sha1.initContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sha1.compressApi with
    name := Spec.Sha1.compressApi.name ++ "_shani"
    target := X86_64.target
    doc := Spec.Sha1.compressApi.doc (notes := ["This implementation uses the SHA extensions."])
    code := Impl.Sha1.X86_64.ShaNi.compress
    contract := Spec.Sha1.compressContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"]
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sha1.X86_64
