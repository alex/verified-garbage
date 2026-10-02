import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances

/-!
# HMAC-SHA-512/256 (RFC 2104) on ARMv7

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-512/256's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha512_256.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := sha512_256H.init
    contract := Spec.Hmac.sha512_256I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Instances.sha512_256_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := sha512_256H.finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Instances.sha512_256_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha512_256.Arm
