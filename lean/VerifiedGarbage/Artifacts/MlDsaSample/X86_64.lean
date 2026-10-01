import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified

/-!
# ML-DSA (FIPS 204) on x86-64: the sampling primitives

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Poly.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSample.X86_64

open VG

def artifacts : List Artifact := [
  { Spec.MlDsa.rejNTTApi with
    target := X86_64.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."])
    code := Impl.MlDsa.X86_64.Sample.rejNTT
    contract := Spec.MlDsa.rejNTTContract X86_64.abi 16
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.rejNTT_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.rejNTT4Api with
    target := X86_64.target
    doc := Spec.MlDsa.rejNTT4Api.doc (notes := ["It calls `vg_mldsa_rej_ntt_poly` on each seed, and saves \
      its caller's callee-saved registers in `scratch`."])
    code := Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    contract := Spec.MlDsa.rejNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlDsa.X86_64.Rej4.rejNTT4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.rejNTT4Api with
    name := Spec.MlDsa.rejNTT4Api.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.rejNTT4Api.doc (notes := ["It runs the four instances of SHAKE128 at once, in the four \
      64-bit elements of AVX2 registers (as `vg_mlkem_sample_ntt4_avx2` does), squeezing three blocks of each \
      twice, and runs the loop of `RejNTTPoly` over the 1008 bytes of each seed's output, as \
      `vg_mldsa_rej_ntt_poly` does. It saves its caller's callee-saved registers in `scratch`."])
    code := Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4Avx2
    contract := Spec.MlDsa.rejNTT4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlDsa.X86_64.Rej4.rejNTT4Avx2_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.rejBoundedApi with
    target := X86_64.target
    doc := Spec.MlDsa.rejBoundedApi.doc (notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing."])
    code := Impl.MlDsa.X86_64.Sample.rejBounded
    contract := Spec.MlDsa.rejBoundedContract X86_64.abi 16
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.rejBounded_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.expandMaskApi with
    target := X86_64.target
    doc := Spec.MlDsa.expandMaskApi.doc (notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."])
    code := Impl.MlDsa.X86_64.Sample.expandMask
    contract := Spec.MlDsa.expandMaskContract X86_64.abi 16
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.expandMask_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.MlDsa.expandMask4Api with
    target := X86_64.target
    doc := Spec.MlDsa.expandMask4Api.doc (notes := ["It calls `vg_mldsa_expand_mask_poly` on each seed, and \
      saves its caller's callee-saved registers in `scratch`."])
    code := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4
    contract := Spec.MlDsa.expandMask4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlDsa.X86_64.Mask4.expandMask4_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.expandMask4Api with
    name := Spec.MlDsa.expandMask4Api.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.expandMask4Api.doc (notes := ["It runs the four instances of SHAKE256 at once, in the \
      four 64-bit elements of AVX2 registers (as `vg_mldsa_rej_ntt_poly4_avx2` does with SHAKE128), \
      squeezing five blocks of each, and unpacks the 576 or 640 bytes of each seed's output as \
      `vg_mldsa_expand_mask_poly` does. It saves its caller's callee-saved registers in `scratch`."])
    code := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4Avx2
    contract := Spec.MlDsa.expandMask4Contract X86_64.abi 24
    stack := 24
    verified := Proof.MlDsa.X86_64.Mask4.expandMask4Avx2_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.sampleInBallApi with
    target := X86_64.target
    doc := Spec.MlDsa.sampleInBallApi.doc (notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits."])
    code := Impl.MlDsa.X86_64.Sample.sampleInBall
    contract := Spec.MlDsa.sampleInBallContract X86_64.abi 16
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.sampleInBall_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.MlDsaSample.X86_64
