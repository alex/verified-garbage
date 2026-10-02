import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances

/-!
# HMAC-MD5 (RFC 2104) on ARMv7

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling MD5's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacMd5.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.initApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.initApi.doc
    code := md5H.init
    contract := Spec.Hmac.md5I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Instances.md5_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.finalizeApi.doc
    code := md5H.finalize
    contract := Spec.Hmac.md5I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Instances.md5_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacMd5.Arm
