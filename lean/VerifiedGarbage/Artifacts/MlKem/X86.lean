import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlKem.X86.Encode12
import VerifiedGarbage.Proof.MlKem.X86.Decode12
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86.NttInv
import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.MlKem.X86.Sample

/-!
# ML-KEM (FIPS 203) on x86

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
`vg_mlkem_sample_ntt` also calls the Keccak functions, each in a frame of its
6 arguments (24 bytes), with the return address and the callee's 12 bytes
below it (`stack := 56`).
-/

namespace VG.Artifacts.MlKem.X86

def artifacts : List Artifact := [
  { Spec.MlKem.addApi with
    target := X86.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86.add
    contract := Spec.MlKem.addContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.add_verified },
  { Spec.MlKem.subApi with
    target := X86.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86.sub
    contract := Spec.MlKem.subContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.sub_verified },
  { Spec.MlKem.encode12Api with
    target := X86.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.X86.encode12
    contract := Spec.MlKem.encode12Contract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.Encode12.verified },
  { Spec.MlKem.decode12Api with
    target := X86.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.X86.decode12
    contract := Spec.MlKem.decode12Contract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.Decode12.verified },
  { Spec.MlKem.cbd2Api with
    target := X86.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.X86.cbd2
    contract := Spec.MlKem.cbd2Contract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.Cbd.verified },
  { Spec.MlKem.compressEncodeApi with
    target := X86.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.X86.compressEncode
    contract := Spec.MlKem.compressEncodeContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.CompressEncode.verified },
  { Spec.MlKem.decodeDecompressApi with
    target := X86.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.X86.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.DecodeDecompress.verified },
  { Spec.MlKem.nttApi with
    target := X86.target
    doc := Spec.MlKem.nttApi.doc
    code := Impl.MlKem.X86.ntt
    contract := Spec.MlKem.nttContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.NttFwd.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttInvApi with
    target := X86.target
    doc := Spec.MlKem.nttInvApi.doc
    code := Impl.MlKem.X86.nttInv
    contract := Spec.MlKem.nttInvContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.NttInvP.verified
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.mulApi with
    target := X86.target
    doc := Spec.MlKem.mulApi.doc
    code := Impl.MlKem.X86.multiplyNTTs
    contract := Spec.MlKem.mulContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.Mul.verified },
  { Spec.MlKem.checkEkApi with
    target := X86.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.X86.checkEk
    contract := Spec.MlKem.checkEkContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.CheckEk.verified },
  { Spec.MlKem.sampleNTTApi with
    target := X86.target
    doc := Spec.MlKem.sampleNTTApi.doc
    code := Impl.MlKem.X86.sampleNTT
    contract := Spec.MlKem.sampleNTTContract X86.abi 56
    stack := 56
    verified := Proof.MlKem.X86.Sample.verified }]

end VG.Artifacts.MlKem.X86
