import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances

/-!
# PBKDF2-HMAC-SHA-1 (RFC 8018) on x86: the iteration and the whole derivation

The code is the one PBKDF2 iteration for every streaming hash function
(`Impl/Pbkdf2/Generic/X86.lean`), calling SHA-1's verified `update` and
`finalize`.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above. `stack` is
that of the shared contracts: 48 bytes for the iteration, and 76 for
`pbkdf2`, which pushes up to 24 bytes of arguments for the functions it
calls, and their return address.
-/

namespace VG.Artifacts.Pbkdf2Sha1.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.iterateApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.iterateApi.doc
    code := Impl.Pbkdf2.Generic.X86.iterate sha1H
    contract := Spec.Hmac.sha1I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 48
    verified := Proof.Pbkdf2.Generic.X86.Instances.sha1
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.pbkdf2Api with
    target := X86.target
    doc := Spec.Hmac.sha1I.pbkdf2Api.doc
    code := Proof.Pbkdf2.Whole.X86.sha1F.pbkdf2
    contract := Spec.Hmac.sha1I.pbkdf2Contract X86.abi 76
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract; rfl⟩
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.sha1
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Pbkdf2Sha1.X86
