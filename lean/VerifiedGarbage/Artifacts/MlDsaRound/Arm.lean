import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Bits
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.Arm.Round.UseHint

/-!
# ML-DSA (FIPS 204) on 32-bit ARM: rounding and hints

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaRound.Arm

open VG.Proof.MlDsa.Arm.Round

def artifacts : List Artifact := [
  { Spec.MlDsa.power2RoundApi with
    target := Arm.target
    doc := Spec.MlDsa.power2RoundApi.doc
      (notes := ["The function saves `r4` on the stack (the 4 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Round.power2Round
    contract := Spec.MlDsa.power2RoundContract Arm.abi 4
    stack := 4
    verified := P2R.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.highBitsApi with
    target := Arm.target
    doc := Spec.MlDsa.highBitsApi.doc
    code := Impl.MlDsa.Arm.Round.highBits
    contract := Spec.MlDsa.highBitsContract Arm.abi
    verified := Bits.high_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.lowBitsApi with
    target := Arm.target
    doc := Spec.MlDsa.lowBitsApi.doc
    code := Impl.MlDsa.Arm.Round.lowBits
    contract := Spec.MlDsa.lowBitsContract Arm.abi
    verified := Bits.low_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.normLtApi with
    target := Arm.target
    doc := Spec.MlDsa.normLtApi.doc
      (notes := ["The function saves `r4` on the stack (the 4 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Round.normLt
    contract := Spec.MlDsa.normLtContract Arm.abi 4
    stack := 4
    verified := NormLt.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.makeHintApi with
    target := Arm.target
    doc := Spec.MlDsa.makeHintApi.doc
      (notes := ["The function saves `r4`–`r6` on the stack (the 12 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Round.makeHint
    contract := Spec.MlDsa.makeHintContract Arm.abi 12
    stack := 12
    verified := MakeHint.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.useHintApi with
    target := Arm.target
    doc := Spec.MlDsa.useHintApi.doc
      (notes := ["The function saves `r4`–`r6` on the stack (the 12 bytes below the stack pointer)."])
    code := Impl.MlDsa.Arm.Round.useHint
    contract := Spec.MlDsa.useHintContract Arm.abi 12
    stack := 12
    verified := UseHint.verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaRound.Arm
