import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances

/-!
# HMAC-SHA-512/256 (RFC 2104) on ARMv7

`init` is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/Arm.lean`), calling SHA-512/256's verified streaming
`init` and `update`.

`finalize` is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`): it finalizes the inner state with SHA-512/256's
verified streaming `finalize`, then computes the outer hash as one call of
SHA-512's verified compression function (`vg_sha512_compress`), on a block
laid out at fixed offsets in `scratch`. It pushes 8 bytes of stack (the stack
arguments of `finalize`); `stack` is that of the shared contract, 16 bytes.
-/

namespace VG.Artifacts.HmacSha512_256.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacInit
    contract := Spec.Hmac.sha512_256I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_256_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha512_256Md.hmacFin
    contract := Spec.Hmac.sha512_256I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha512_256.Arm
