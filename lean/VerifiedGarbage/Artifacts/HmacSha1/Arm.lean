import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances

/-!
# HMAC-SHA-1 (RFC 2104) on ARMv7

`init` is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-1's verified streaming `init` and
`update`.

`finalize` is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): it finalizes the inner state with SHA-1's
verified streaming `finalize`, then computes the outer hash as one call of
SHA-1's verified compression function (`vg_sha1_compress`), on a block laid
out at fixed offsets in `scratch`. It pushes 8 bytes of stack (the stack
arguments of `finalize`); `stack` is that of the shared contract, 16 bytes.
-/

namespace VG.Artifacts.HmacSha1.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha1Md.hmacInit
    contract := Spec.Hmac.sha1I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha1_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha1I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha1Md.hmacFin
    contract := Spec.Hmac.sha1I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha1.Arm
