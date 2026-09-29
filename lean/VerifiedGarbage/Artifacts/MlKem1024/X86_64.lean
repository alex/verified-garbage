import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk

/-!
# ML-KEM-1024 (FIPS 203) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem1024.X86_64

def artifacts : List Artifact := [
  { Spec.MlKem1024.compressEncodeApi with
    target := X86_64.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.X86_64.compressEncode1024
    contract := Spec.MlKem1024.compressEncodeContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.compressEncode1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.decodeDecompressApi with
    target := X86_64.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.X86_64.decodeDecompress1024
    contract := Spec.MlKem1024.decodeDecompressContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.decodeDecompress1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.checkEkApi with
    target := X86_64.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.X86_64.checkEk1024
    contract := Spec.MlKem1024.checkEkContract X86_64.abi
    verified := Proof.MlKem1024.X86_64.checkEk1024_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKem1024.X86_64
