import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub

/-!
# ML-DSA (FIPS 204) on x86-64: the arithmetic of polynomials

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaArith.X86_64

def artifacts : List Artifact := [
  { Spec.MlDsa.nttApi with
    target := X86_64.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."])
    code := Impl.MlDsa.X86_64.Arith.ntt
    contract := Spec.MlDsa.nttContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.ntt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.nttInvApi with
    target := X86_64.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."])
    code := Impl.MlDsa.X86_64.Arith.nttInv
    contract := Spec.MlDsa.nttInvContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.nttInv_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.mulApi with
    target := X86_64.target
    doc := Spec.MlDsa.mulApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."])
    code := Impl.MlDsa.X86_64.Arith.mul
    contract := Spec.MlDsa.mulContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.mul_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.mulAddApi with
    target := X86_64.target
    doc := Spec.MlDsa.mulAddApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."])
    code := Impl.MlDsa.X86_64.Arith.mulAdd
    contract := Spec.MlDsa.mulAddContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.mulAdd_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.addApi with
    target := X86_64.target
    doc := Spec.MlDsa.addApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers."])
    code := Impl.MlDsa.X86_64.Arith.add
    contract := Spec.MlDsa.addContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.add_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.subApi with
    target := X86_64.target
    doc := Spec.MlDsa.subApi.doc
      (notes := ["The function computes on four coefficients at a time in SSE2 registers."])
    code := Impl.MlDsa.X86_64.Arith.sub
    contract := Spec.MlDsa.subContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.sub_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.nttApi with
    name := Spec.MlDsa.nttApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."])
    code := Impl.MlDsa.X86_64.Arith.nttAvx2
    contract := Spec.MlDsa.nttContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.nttY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"]
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.nttInvApi with
    name := Spec.MlDsa.nttInvApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers, with a table of \
        the 256 zetas that it stores in `scratch`. It sets MXCSR to `0x1FBF` around its multiplications \
        (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the caller's MXCSR back \
        before returning."])
    code := Impl.MlDsa.X86_64.Arith.nttInvAvx2
    contract := Spec.MlDsa.nttInvContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.nttInvY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"]
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.mulApi with
    name := Spec.MlDsa.mulApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.mulApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."])
    code := Impl.MlDsa.X86_64.Arith.mulAvx2
    contract := Spec.MlDsa.mulContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.mulY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.mulAddApi with
    name := Spec.MlDsa.mulAddApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.mulAddApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers. It sets MXCSR to \
        `0x1FBF` around its multiplications (Intel's mitigation of MXCSR-configuration-dependent timing), \
        through the last 8 bytes of `h`, which it stores last, and loads the caller's MXCSR back before \
        returning."])
    code := Impl.MlDsa.X86_64.Arith.mulAddAvx2
    contract := Spec.MlDsa.mulAddContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.mulAddY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.addApi with
    name := Spec.MlDsa.addApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.addApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers."])
    code := Impl.MlDsa.X86_64.Arith.addAvx2
    contract := Spec.MlDsa.addContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.addY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.subApi with
    name := Spec.MlDsa.subApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.subApi.doc
      (notes := ["The function computes on eight coefficients at a time in AVX2 registers."])
    code := Impl.MlDsa.X86_64.Arith.subAvx2
    contract := Spec.MlDsa.subContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Arith.subY_verified
    spSafe := Code.all_of_allInstrs (by lit_decide)
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlDsaArith.X86_64
