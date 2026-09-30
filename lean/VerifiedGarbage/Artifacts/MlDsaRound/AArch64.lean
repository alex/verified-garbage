import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint

/-!
# ML-DSA (FIPS 204) on AArch64: rounding and hints

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there. The emitter adds the `# Safety` items that
depend on the target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which
`ofSig` checks against the contract.
-/

namespace VG.Artifacts.MlDsaRound.AArch64

open VG.Proof.MlDsa.AArch64.Round

def artifacts : List Artifact := [
  { Spec.MlDsa.power2RoundApi with
    target := AArch64.target
    doc := Spec.MlDsa.power2RoundApi.doc
    code := Impl.MlDsa.AArch64.Round.power2Round
    contract := Spec.MlDsa.power2RoundContract AArch64.abi
    verified := power2Round_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.highBitsApi with
    target := AArch64.target
    doc := Spec.MlDsa.highBitsApi.doc
    code := Impl.MlDsa.AArch64.Round.highBits
    contract := Spec.MlDsa.highBitsContract AArch64.abi
    verified := highBits_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.lowBitsApi with
    target := AArch64.target
    doc := Spec.MlDsa.lowBitsApi.doc
    code := Impl.MlDsa.AArch64.Round.lowBits
    contract := Spec.MlDsa.lowBitsContract AArch64.abi
    verified := lowBits_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.normLtApi with
    target := AArch64.target
    doc := Spec.MlDsa.normLtApi.doc
    code := Impl.MlDsa.AArch64.Round.normLt
    contract := Spec.MlDsa.normLtContract AArch64.abi
    verified := normLt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.makeHintApi with
    target := AArch64.target
    doc := Spec.MlDsa.makeHintApi.doc
    code := Impl.MlDsa.AArch64.Round.makeHint
    contract := Spec.MlDsa.makeHintContract AArch64.abi
    verified := makeHint_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.useHintApi with
    target := AArch64.target
    doc := Spec.MlDsa.useHintApi.doc
    code := Impl.MlDsa.AArch64.Round.useHint
    contract := Spec.MlDsa.useHintContract AArch64.abi
    verified := useHint_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaRound.AArch64
