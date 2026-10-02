import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey

/-! # AES on ARMv7 -/

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := Arm.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.Arm.expandKey
    contract := Spec.Aes.expandKeyContract Arm.abi
    verified := Proof.Aes.Arm.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    target := Arm.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.Arm.ctr32
    contract := Spec.Gcm.ctr32Contract Arm.abi
    verified := Proof.Aes.Arm.ctr32_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Aes.Arm
