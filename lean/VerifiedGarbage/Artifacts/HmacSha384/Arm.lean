import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances

/-!
# HMAC-SHA-384 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-384's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-384's
verified compression function.

`finalize` finalizes the inner state with SHA-384's verified streaming
`finalize`, then computes the outer hash as one call of SHA-512's verified
compression function (`vg_sha512_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.
-/

namespace VG.Artifacts.HmacSha384.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha384I.initApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha384Md.hmacInit
    contract := Spec.Hmac.sha384I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha384_init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.sha384I.finalizeApi with
    target := Arm.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha384Md.hmacFin
    contract := Spec.Hmac.sha384I.finalizeContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.HmacSha384.Arm
