import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances

/-!
# PBKDF2-HMAC-MD5 (RFC 8018) on ARMv7: the iteration and the whole derivation

The code is the one PBKDF2 iteration for every streaming hash function
(`Impl/Pbkdf2/Generic/Arm.lean`), calling MD5's verified `update` and
`finalize`.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/Arm.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contracts: 16 bytes for the iteration, and 24 for
`pbkdf2`, which pushes `update`'s 16 bytes of stack arguments, or 8 bytes
around a call of a function that uses 16.
-/

namespace VG.Artifacts.Pbkdf2Md5.Arm

open VG.Proof.Hmac.Generic.Arm

def artifacts : List Artifact := [
  { Spec.Hmac.md5I.iterateApi with
    target := Arm.target
    doc := Spec.Hmac.md5I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.Arm.iterate md5H
    contract := Spec.Hmac.md5I.iterateContract Arm.abi 16
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 16
    verified := Proof.Pbkdf2.Generic.Arm.Instances.md5
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Hmac.md5I.pbkdf2Api with
    target := Arm.target
    doc := Spec.Hmac.md5I.pbkdf2Api.doc
    code := Proof.Pbkdf2.Whole.Arm.md5F.pbkdf2
    contract := Spec.Hmac.md5I.pbkdf2Contract Arm.abi 24
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 24
    verified := Proof.Pbkdf2.Whole.Arm.md5
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Pbkdf2Md5.Arm
