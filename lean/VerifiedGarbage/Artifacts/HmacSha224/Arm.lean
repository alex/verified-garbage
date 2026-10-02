import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Sha224

/-!
# HMAC-SHA-224 (RFC 2104) on ARMv7

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-224's verified `init` and
SHA-256's `update` and `finalize`.
-/

namespace VG.Artifacts.HmacSha224.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha224I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.initApi.doc
    code := sha224H.init
    contract := Spec.Hmac.sha224I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha224_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha224I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.finalizeApi.doc
    code := sha224H.finalize
    contract := Spec.Hmac.sha224I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Instances.sha224_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha224.Arm
