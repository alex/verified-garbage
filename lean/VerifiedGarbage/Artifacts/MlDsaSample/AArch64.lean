import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

/-!
# ML-DSA (FIPS 204) on AArch64: the sampling primitives

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Poly.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSample.AArch64

open VG

def artifacts : List Artifact := [
  { Spec.MlDsa.rejNTTApi with
    target := AArch64.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."])
    code := Impl.MlDsa.AArch64.Sample.rejNTT
    contract := Spec.MlDsa.rejNTTContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejNTT_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.rejBoundedApi with
    target := AArch64.target
    doc := Spec.MlDsa.rejBoundedApi.doc (notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of a half-byte is computed and stored \
      without a branch or a table, and counted only if the half-byte is accepted, so only whether each \
      half-byte is accepted affects timing."])
    code := Impl.MlDsa.AArch64.Sample.rejBounded
    contract := Spec.MlDsa.rejBoundedContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.rejBounded_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.expandMaskApi with
    target := AArch64.target
    doc := Spec.MlDsa.expandMaskApi.doc (notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."])
    code := Impl.MlDsa.AArch64.Sample.expandMask
    contract := Spec.MlDsa.expandMaskContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.expandMask_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sampleInBallApi with
    target := AArch64.target
    doc := Spec.MlDsa.sampleInBallApi.doc (notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits."])
    code := Impl.MlDsa.AArch64.Sample.sampleInBall
    contract := Spec.MlDsa.sampleInBallContract AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Sample.sampleInBall_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaSample.AArch64
