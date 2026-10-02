import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances

/-!
# HMAC-SHA-384 (RFC 2104) on x86

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86.lean`), calling SHA-384's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha384.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha384I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha384I.initApi.doc
    code := sha384H.init
    contract := Spec.Hmac.sha384I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Instances.sha384_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha384I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha384I.finalizeApi.doc
    code := sha384H.finalize
    contract := Spec.Hmac.sha384I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Instances.sha384_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha384.X86
