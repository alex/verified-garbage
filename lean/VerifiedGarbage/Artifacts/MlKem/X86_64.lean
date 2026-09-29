import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM (FIPS 203) on x86-64: the polynomial primitives and ML-KEM-768

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  { Spec.MlKem.nttApi with
    target := X86_64.target
    doc := Spec.MlKem.nttApi.doc
    code := Impl.MlKem.X86_64.ntt
    contract := Spec.MlKem.nttContract X86_64.abi
    verified := Proof.MlKem.X86_64.ntt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttInvApi with
    target := X86_64.target
    doc := Spec.MlKem.nttInvApi.doc
    code := Impl.MlKem.X86_64.nttInv
    contract := Spec.MlKem.nttInvContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttInv_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.addApi with
    target := X86_64.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86_64.add
    contract := Spec.MlKem.addContract X86_64.abi
    verified := Proof.MlKem.X86_64.add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.subApi with
    target := X86_64.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86_64.sub
    contract := Spec.MlKem.subContract X86_64.abi
    verified := Proof.MlKem.X86_64.sub_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.mulApi with
    target := X86_64.target
    doc := Spec.MlKem.mulApi.doc
    code := Impl.MlKem.X86_64.multiplyNTTs
    contract := Spec.MlKem.mulContract X86_64.abi
    verified := Proof.MlKem.X86_64.mul_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.sampleNTTApi with
    target := X86_64.target
    doc := Spec.MlKem.sampleNTTApi.doc
    code := Impl.MlKem.X86_64.sampleNTT
    contract := Spec.MlKem.sampleNTTContract X86_64.abi 16
    stack := 16
    verified := Proof.MlKem.X86_64.sample_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.encode12Api with
    target := X86_64.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.X86_64.encode12
    contract := Spec.MlKem.encode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.encode12_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.decode12Api with
    target := X86_64.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.X86_64.decode12
    contract := Spec.MlKem.decode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.decode12_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.cbd2Api with
    target := X86_64.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.X86_64.cbd2
    contract := Spec.MlKem.cbd2Contract X86_64.abi
    verified := Proof.MlKem.X86_64.cbd2_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.compressEncodeApi with
    target := X86_64.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.X86_64.compressEncode
    contract := Spec.MlKem.compressEncodeContract X86_64.abi
    verified := Proof.MlKem.X86_64.compressEncode_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.decodeDecompressApi with
    target := X86_64.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.X86_64.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract X86_64.abi
    verified := Proof.MlKem.X86_64.decodeDecompress_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.checkEkApi with
    target := X86_64.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.X86_64.checkEk
    contract := Spec.MlKem.checkEkContract X86_64.abi
    verified := Proof.MlKem.X86_64.checkEk_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.keyGenApi with
    target := X86_64.target
    doc := Spec.MlKem.keyGenApi.doc
      (notes := ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 24 \
        bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.keyGen
    contract := Spec.MlKem.keyGenContract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.keyGen_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.encapsApi with
    target := X86_64.target
    doc := Spec.MlKem.encapsApi.doc
      (notes := ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 24 \
        bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.encaps
    contract := Spec.MlKem.encapsContract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.encaps_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.decapsApi with
    target := X86_64.target
    doc := Spec.MlKem.decapsApi.doc
      (notes := ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 24 \
        bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.decaps
    contract := Spec.MlKem.decapsContract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.decaps_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKem.X86_64
