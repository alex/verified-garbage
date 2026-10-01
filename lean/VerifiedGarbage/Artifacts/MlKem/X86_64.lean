import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-!
# ML-KEM (FIPS 203) on x86-64: the polynomial primitives

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
      (notes := ["The function computes on eight coefficients at a time in SSE2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.ntt
    contract := Spec.MlKem.nttContract X86_64.abi
    verified := Proof.MlKem.X86_64.ntt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttInvApi with
    target := X86_64.target
    doc := Spec.MlKem.nttInvApi.doc
      (notes := ["The function computes on eight coefficients at a time in SSE2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.nttInv
    contract := Spec.MlKem.nttInvContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttInv_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttApi with
    name := Spec.MlKem.nttApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.nttApi.doc
      (notes := ["The function computes on sixteen coefficients at a time in AVX2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.nttAvx2
    contract := Spec.MlKem.nttContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"]
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.nttInvApi with
    name := Spec.MlKem.nttInvApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.nttInvApi.doc
      (notes := ["The function computes on sixteen coefficients at a time in AVX2 registers. It sets MXCSR \
        to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.nttInvAvx2
    contract := Spec.MlKem.nttInvContract X86_64.abi
    verified := Proof.MlKem.X86_64.nttInvY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"]
    ofSig := ⟨_, _, _, by unfold Spec.MlKem.nttInvContract Spec.MlKem.inPlaceContract; rfl⟩ },
  { Spec.MlKem.addApi with
    target := X86_64.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86_64.add
    contract := Spec.MlKem.addContract X86_64.abi
    verified := Proof.MlKem.X86_64.add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.subApi with
    target := X86_64.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86_64.sub
    contract := Spec.MlKem.subContract X86_64.abi
    verified := Proof.MlKem.X86_64.sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.mulApi with
    target := X86_64.target
    doc := Spec.MlKem.mulApi.doc
      (notes := ["The function computes on eight pairs of coefficients at a time in SSE2 registers. It sets \
        MXCSR to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.multiplyNTTs
    contract := Spec.MlKem.mulContract X86_64.abi
    verified := Proof.MlKem.X86_64.mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.mulApi with
    name := Spec.MlKem.mulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.mulApi.doc
      (notes := ["The function computes on sixteen pairs of coefficients at a time in AVX2 registers. It sets \
        MXCSR to `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent \
        timing) and loads the caller's MXCSR back before returning."])
    code := Impl.MlKem.X86_64.multiplyNTTsAvx2
    contract := Spec.MlKem.mulContract X86_64.abi
    verified := Proof.MlKem.X86_64.mulY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlKem.sampleNTTApi with
    target := X86_64.target
    doc := Spec.MlKem.sampleNTTApi.doc
    code := Impl.MlKem.X86_64.sampleNTT
    contract := Spec.MlKem.sampleNTTContract X86_64.abi 16
    stack := 16
    verified := Proof.MlKem.X86_64.sample_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.encode12Api with
    target := X86_64.target
    doc := Spec.MlKem.encode12Api.doc
    code := Impl.MlKem.X86_64.encode12
    contract := Spec.MlKem.encode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.encode12_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decode12Api with
    target := X86_64.target
    doc := Spec.MlKem.decode12Api.doc
    code := Impl.MlKem.X86_64.decode12
    contract := Spec.MlKem.decode12Contract X86_64.abi
    verified := Proof.MlKem.X86_64.decode12_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.cbd2Api with
    target := X86_64.target
    doc := Spec.MlKem.cbd2Api.doc
    code := Impl.MlKem.X86_64.cbd2
    contract := Spec.MlKem.cbd2Contract X86_64.abi
    verified := Proof.MlKem.X86_64.cbd2_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.compressEncodeApi with
    target := X86_64.target
    doc := Spec.MlKem.compressEncodeApi.doc
    code := Impl.MlKem.X86_64.compressEncode
    contract := Spec.MlKem.compressEncodeContract X86_64.abi
    verified := Proof.MlKem.X86_64.compressEncode_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.decodeDecompressApi with
    target := X86_64.target
    doc := Spec.MlKem.decodeDecompressApi.doc
    code := Impl.MlKem.X86_64.decodeDecompress
    contract := Spec.MlKem.decodeDecompressContract X86_64.abi
    verified := Proof.MlKem.X86_64.decodeDecompress_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.checkEkApi with
    target := X86_64.target
    doc := Spec.MlKem.checkEkApi.doc
    code := Impl.MlKem.X86_64.checkEk
    contract := Spec.MlKem.checkEkContract X86_64.abi
    verified := Proof.MlKem.X86_64.checkEk_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlKem.sampleNTT4Api with
    target := X86_64.target
    doc := Spec.MlKem.sampleNTT4Api.doc
      (notes := ["The function calls `vg_mlkem_sample_ntt` on each seed, with 24 bytes of stack below its \
        return address."])
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4
    contract := Spec.MlKem.sampleNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_scalar_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.sampleNTT4Api with
    name := Spec.MlKem.sampleNTT4Api.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlKem.sampleNTT4Api.doc
      (notes := ["The function absorbs the four seeds and squeezes the four instances of SHAKE128 at once, \
        each 64-bit lane of the Keccak states in a 256-bit AVX2 register holding that lane of all four; \
        it then parses the output of each in turn, and finishes any that needs more than the 504 bytes \
        it squeezed with `vg_mlkem_sample_ntt`, with 24 bytes of stack below its return address."])
    code := Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2
    contract := Spec.MlKem.sampleNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlKem.X86_64.sample4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlKem.X86_64
