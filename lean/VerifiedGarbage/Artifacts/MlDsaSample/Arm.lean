import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT

/-!
# ML-DSA (FIPS 204) on 32-bit ARM: the sampling primitives

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Poly.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSample.Arm

open VG

/-- The note shared by the four functions. -/
private def saveNote : String :=
  "The function saves `r4`–`r11` and its return address in `scratch`; the 8 bytes of stack below the stack \
    pointer hold the stack arguments of the SHA-3 functions it calls."

def artifacts : List Artifact := [
  { Spec.MlDsa.rejNTTApi with
    target := Arm.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them.", saveNote])
    code := Impl.MlDsa.Arm.Sample.rejNTT
    contract := Spec.MlDsa.rejNTTContract Arm.abi 8
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejNTT_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.rejBoundedApi with
    target := Arm.target
    doc := Spec.MlDsa.rejBoundedApi.doc (notes := ["It squeezes 544 bytes of SHAKE256 output (4 blocks) and \
      runs the loop of `RejBoundedPoly` over them. The coefficient of an accepted half-byte is computed \
      without a branch or a table, so only whether each half-byte is accepted affects timing.", saveNote])
    code := Impl.MlDsa.Arm.Sample.rejBounded
    contract := Spec.MlDsa.rejBoundedContract Arm.abi 8
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.rejBounded_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.expandMaskApi with
    target := Arm.target
    doc := Spec.MlDsa.expandMaskApi.doc (notes := ["It squeezes 640 bytes of SHAKE256 output (5 blocks, \
      which hold the 576 or 640 bytes it unpacks) and unpacks them with the loop of \
      `vg_mldsa_bit_unpack`.", saveNote])
    code := Impl.MlDsa.Arm.Sample.expandMask
    contract := Spec.MlDsa.expandMaskContract Arm.abi 8
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.expandMask_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sampleInBallApi with
    target := Arm.target
    doc := Spec.MlDsa.sampleInBallApi.doc (notes := ["It squeezes 272 bytes of SHAKE256 output (2 blocks) and \
      runs the loop of `SampleInBall` over the 264 after the sign bits.", saveNote])
    code := Impl.MlDsa.Arm.Sample.sampleInBall
    contract := Spec.MlDsa.sampleInBallContract Arm.abi 8
    stack := 8
    verified := Proof.MlDsa.Arm.Sample.sampleInBall_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaSample.Arm
