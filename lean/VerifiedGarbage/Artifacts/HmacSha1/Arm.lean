import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances

/-!
# HMAC-SHA-1 (RFC 2104) on ARMv7

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-1's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha1.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := sha1H.init
    contract := Spec.Hmac.sha1I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Instances.sha1_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha1I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := sha1H.finalize
    contract := Spec.Hmac.sha1I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Instances.sha1_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha1.Arm
