import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Impl.Hmac.Sha256.X86
import VerifiedGarbage.Impl.Pbkdf2.Sha256.X86
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Spec.Hmac.Contract
import VerifiedGarbage.Spec.Pbkdf2.Contract
import VerifiedGarbage.Spec.Hmac.Generic

/-!
# PBKDF2-HMAC-SHA-256 on x86 (32-bit), the whole derivation: the functions it calls

SHA-256 has backends on x86 (`Proof/Sha256/X86/Variants/Interface.lean`): its
streaming `update` and `finalize`, HMAC's `init` and `finalize` and PBKDF2's
`iterate` call the backend's compression function. The whole derivation
(`Impl/Pbkdf2/Whole/X86.lean`) calls them, by the names the generic
registration files give them (with the backend's suffix).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)

/-- SHA-256's streaming functions, with the backend's `update` and
`finalize` (`updC`, `finC`) and suffix. -/
def sha256H (suffix : String) (updC finC : Prog isa) : Impl.Hmac.Generic.X86.Hash :=
  ⟨64, 96, 32, 32, 20, Spec.Sha256.initApi.name, Impl.Sha256.X86.Stream.init,
    Spec.Sha256.updateApi.name ++ suffix, updC, Spec.Sha256.finalizeApi.name ++ suffix, finC⟩

/-- The functions `pbkdf2` calls for SHA-256, with the compression function
`cmpN`/`cmpC` and the streaming `update` and `finalize` calling it. -/
def sha256Fns (suffix cmpN : String) (cmpC updC finC : Prog isa) : Fns where
  H := sha256H suffix updC finC
  W := Spec.Hmac.sha256I.scratch
  hiN := Spec.Hmac.initSha256Api.name ++ suffix
  hiC := Impl.Hmac.Sha256.X86.init cmpN cmpC
  hfN := Spec.Hmac.finalizeSha256OutApi.name ++ suffix
  hfC := Impl.Hmac.Sha256.X86.finalize cmpN cmpC
  itN := Spec.Pbkdf2.iterateSha256Api.name ++ suffix
  itC := Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC

end VG.Proof.Pbkdf2.Whole.X86
