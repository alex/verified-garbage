import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
import VerifiedGarbage.Proof.MlKem1024.X86.KeyGen
import VerifiedGarbage.Proof.MlKem1024.X86.Encaps
import VerifiedGarbage.Proof.MlKem1024.X86.Decaps

/-!
# ML-KEM-1024 (FIPS 203) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions that call no other one save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
`vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps` save
their caller's registers in 16 bytes, and call `vg_mlkem_sample_ntt` in a
frame of its 3 arguments (12 bytes), with the return address and the
callee's 56 bytes below it (`stack := 88`); their other calls use less.
-/

namespace VG.Artifacts.MlKem1024.X86

def artifacts : List Artifact := [
  { Spec.MlKem1024.compressEncodeApi with
    target := X86.target
    doc := Spec.MlKem1024.compressEncodeApi.doc
    code := Impl.MlKem1024.X86.compressEncode
    contract := Spec.MlKem1024.compressEncodeContract X86.abi 16
    stack := 16
    verified := Proof.MlKem1024.X86.CompressEncode.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.decodeDecompressApi with
    target := X86.target
    doc := Spec.MlKem1024.decodeDecompressApi.doc
    code := Impl.MlKem1024.X86.decodeDecompress
    contract := Spec.MlKem1024.decodeDecompressContract X86.abi 16
    stack := 16
    verified := Proof.MlKem1024.X86.DecodeDecompress.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.checkEkApi with
    target := X86.target
    doc := Spec.MlKem1024.checkEkApi.doc
    code := Impl.MlKem1024.X86.checkEk
    contract := Spec.MlKem1024.checkEkContract X86.abi 16
    stack := 16
    verified := Proof.MlKem1024.X86.CheckEk.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.keyGenApi with
    target := X86.target
    doc := Spec.MlKem1024.keyGenApi.doc
    code := Impl.MlKem1024.X86.keyGen
    contract := Spec.MlKem1024.keyGenContract X86.abi 88
    stack := 88
    verified := Proof.MlKem1024.X86.KeyGen.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.encapsApi with
    target := X86.target
    doc := Spec.MlKem1024.encapsApi.doc
    code := Impl.MlKem1024.X86.encaps
    contract := Spec.MlKem1024.encapsContract X86.abi 88
    stack := 88
    verified := Proof.MlKem1024.X86.Encaps.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem1024.decapsApi with
    target := X86.target
    doc := Spec.MlKem1024.decapsApi.doc
    code := Impl.MlKem1024.X86.decaps
    contract := Spec.MlKem1024.decapsContract X86.abi 88
    stack := 88
    verified := Proof.MlKem1024.X86.Decaps.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKem1024.X86
