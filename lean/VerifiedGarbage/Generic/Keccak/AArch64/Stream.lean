import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze

namespace VG.Generic.Keccak.AArch64.Stream

/-- Every sponge entry point follows every registered permutation backend. -/
def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.Sha3.absorbApi with
    name := Spec.Sha3.absorbApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.Sha3.AArch64.Stream.absorbWith v.callee
    contract := Spec.Sha3.absorbContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Absorb.absorb_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    name := Spec.Sha3.padApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.Sha3.AArch64.Stream.padWith v.callee
    contract := Spec.Sha3.padContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Pad.pad_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    name := Spec.Sha3.squeezeApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.Sha3.AArch64.Stream.squeezeWith v.callee
    contract := Spec.Sha3.squeezeContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.Stream
