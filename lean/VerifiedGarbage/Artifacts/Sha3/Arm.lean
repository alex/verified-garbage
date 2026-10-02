import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha3.Arm.Shared

/-! # SHA-3 and SHAKE (FIPS 202) on 32-bit ARM -/

namespace VG.Artifacts.Sha3.Arm

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := Arm.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.Arm.permute
    contract := Spec.Sha3.permuteContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.permute
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.absorbApi with
    target := Arm.target
    doc := Spec.Sha3.absorbApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.absorb
    contract := Spec.Sha3.absorbContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.absorb
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    target := Arm.target
    doc := Spec.Sha3.padApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.pad
    contract := Spec.Sha3.padContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.pad
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    target := Arm.target
    doc := Spec.Sha3.squeezeApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Sha3.Arm.Stream.squeeze
    contract := Spec.Sha3.squeezeContract Arm.abi
    verified := Proof.Sha3.Arm.Shared.squeeze
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha3.Arm
