import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Arm.Finalize
import VerifiedGarbage.Proof.Hmac.Arm.Init

/-! # HMAC-SHA-256 (RFC 2104) on ARMv7 -/

namespace VG.Artifacts.HmacSha256.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.initSha256Api with
    target := Arm.target
    doc := Spec.Hmac.initSha256Api.doc
    code := Impl.Hmac.Arm.init
    contract := Spec.Hmac.initSha256Contract Arm.abi
    verified := Proof.Hmac.Arm.Init.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.finalizeSha256OutApi with
    target := Arm.target
    doc := Spec.Hmac.finalizeSha256OutApi.doc
    code := Impl.Hmac.Arm.finalize
    contract := Spec.Hmac.finalizeSha256OutContract Arm.abi
    verified := Proof.Hmac.Arm.Finalize.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha256.Arm
