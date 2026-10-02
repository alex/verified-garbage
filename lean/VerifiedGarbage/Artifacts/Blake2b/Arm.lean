import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Blake2.Arm.Blake2b

/-! # BLAKE2b (RFC 7693) on ARMv7 -/

namespace VG.Artifacts.Blake2b.Arm

def artifacts : List Artifact := [
  { Spec.Blake2.compressBApi with
    target := Arm.target
    doc := Spec.Blake2.compressBApi.doc
    code := Impl.Blake2.Arm.B.compress
    contract := Spec.Blake2.compressBContract Arm.abi
    verified := Proof.Blake2.ArmB.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.initBApi with
    target := Arm.target
    doc := Spec.Blake2.initBApi.doc
    code := Impl.Blake2.Arm.Stream.init Spec.Blake2.b
    contract := Spec.Blake2.initBContract Arm.abi
    verified := Proof.Blake2.ArmB.initB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.updateBApi with
    target := Arm.target
    doc := Spec.Blake2.updateBApi.doc
    code := Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress
    contract := Spec.Blake2.updateBContract Arm.abi 16
    stack := 16
    verified := Proof.Blake2.ArmB.updateB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.finalizeBApi with
    target := Arm.target
    doc := Spec.Blake2.finalizeBApi.doc
    code := Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress
    contract := Spec.Blake2.finalizeBContract Arm.abi 16
    stack := 16
    verified := Proof.Blake2.ArmB.finalizeB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blake2b.Arm
