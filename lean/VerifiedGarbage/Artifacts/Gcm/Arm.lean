import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Gcm.Arm.Ghash

/-! # GHASH on ARMv7 -/

namespace VG.Artifacts.Gcm.Arm

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := Arm.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.Arm.ghash
    contract := Spec.Gcm.ghashContract Arm.abi
    verified := Proof.Gcm.Arm.ghash_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gcm.Arm
