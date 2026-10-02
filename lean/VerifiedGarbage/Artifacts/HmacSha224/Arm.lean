import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224

/-!
# HMAC-SHA-224 (RFC 2104) on ARMv7

`init` is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-224's verified streaming `init`
and SHA-256's `update`.

`finalize` is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): it finalizes the inner state with SHA-256's
verified streaming `finalize`, then computes the outer hash as one call of
SHA-256's verified compression function (`vg_sha256_compress`), on a block
laid out at fixed offsets in `scratch`. It pushes 8 bytes of stack (the stack
arguments of `finalize`); `stack` is that of the shared contract, 16 bytes.
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
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacFin
    contract := Spec.Hmac.sha224I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha224.Arm
