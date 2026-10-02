import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224

/-!
# HMAC-SHA-224 (RFC 2104) on ARMv7

`init` and `finalize` are the ones for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/Arm.lean`). `init` sets both states' hash values with
SHA-224's verified streaming `init`, writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` word
by word into their buffers, and absorbs each with one call of SHA-256's
verified compression function (`vg_sha256_compress`).

`finalize` finalizes the inner state with SHA-256's verified streaming
`finalize`, then computes the outer hash as one call of SHA-256's verified
compression function (`vg_sha256_compress`), on a block laid out at fixed
offsets in `scratch`. It pushes 8 bytes of stack (the stack arguments of
`finalize`); `stack` is that of the shared contract, 16 bytes.
-/

namespace VG.Artifacts.HmacSha224.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.sha224I.initApi with
    target := Arm.target
    doc := Spec.Hmac.sha224I.initApi.doc
    code := Proof.Pbkdf2.Md.Arm.sha224Md.hmacInit
    contract := Spec.Hmac.sha224I.initContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    writeArgs := true
    stack := 16
    verified := Proof.Pbkdf2.Md.Arm.Instances.sha224_init
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
