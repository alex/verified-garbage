import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.X86.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop

/-!
# ML-DSA (FIPS 204) on x86: the sampling primitives

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Poly.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function saves its caller's registers in a frame of 16 bytes below the
return address, and calls the Keccak functions, each in a frame of its 5 or
6 arguments (at most 24 bytes), with the return address and the callee's 12
bytes below it (`stack := 56`), as `vg_mlkem_sample_ntt` does.
-/

namespace VG.Artifacts.MlDsaSample.X86

open VG

def artifacts : List Artifact := [
  { Spec.MlDsa.rejNTTApi with
    target := X86.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."])
    code := Impl.MlDsa.X86.Sample.rejNTT
    contract := Spec.MlDsa.rejNTTContract X86.abi 56
    stack := 56
    verified := Proof.MlDsa.X86.Sample.RejNtt.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.rejBoundedApi with
    target := X86.target
    doc := Spec.MlDsa.rejBoundedApi.doc (notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing."])
    code := Impl.MlDsa.X86.Sample.rejBounded
    contract := Spec.MlDsa.rejBoundedContract X86.abi 56
    stack := 56
    verified := Proof.MlDsa.X86.Sample.RejBounded.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.expandMaskApi with
    target := X86.target
    doc := Spec.MlDsa.expandMaskApi.doc (notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks four coefficients at a time."])
    code := Impl.MlDsa.X86.Sample.expandMask
    contract := Spec.MlDsa.expandMaskContract X86.abi 56
    stack := 56
    verified := Proof.MlDsa.X86.Sample.ExpandMask.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.sampleInBallApi with
    target := X86.target
    doc := Spec.MlDsa.sampleInBallApi.doc (notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits, which it keeps, as two words, in the \
      argument slots of `len` and `tau`."])
    code := Impl.MlDsa.X86.Sample.sampleInBall
    contract := Spec.MlDsa.sampleInBallContract X86.abi 56
    stack := 56
    verified := Proof.MlDsa.X86.Sample.Ball.verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaSample.X86
