import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances

/-!
# HMAC-SHA-1 (RFC 2104) on x86

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86.lean`), calling SHA-1's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha1.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha1I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.initApi.doc
    code := sha1H.init
    contract := Spec.Hmac.sha1I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Instances.sha1_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha1I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha1I.finalizeApi.doc
    code := sha1H.finalize
    contract := Spec.Hmac.sha1I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Instances.sha1_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha1.X86
