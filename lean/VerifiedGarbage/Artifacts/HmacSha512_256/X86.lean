import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances

/-!
# HMAC-SHA-512/256 (RFC 2104) on x86

The code is the one HMAC implementation for every streaming hash function
(`Impl/Hmac/Generic/X86.lean`), calling SHA-512/256's verified `init`, `update`
and `finalize`.
-/

namespace VG.Artifacts.HmacSha512_256.X86

open VG.Proof.Hmac.Generic.X86

def artifacts : List Artifact := [
  { Spec.Hmac.sha512_256I.initApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.initApi.doc
    code := sha512_256H.init
    contract := Spec.Hmac.sha512_256I.initContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.initContract; rfl⟩
    stack := 48
    verified := Instances.sha512_256_init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Hmac.sha512_256I.finalizeApi with
    target := X86.target
    doc := Spec.Hmac.sha512_256I.finalizeApi.doc
    code := sha512_256H.finalize
    contract := Spec.Hmac.sha512_256I.finalizeContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.finalizeContract; rfl⟩
    stack := 48
    verified := Instances.sha512_256_finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.HmacSha512_256.X86
