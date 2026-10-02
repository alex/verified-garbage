import VerifiedGarbage.Proof.Hmac.Generic.X86.Lit
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its code as literals

For each hash function of `Proof/Hmac/Generic/X86/Hashes.lean`, the functions
`pbkdf2` calls (`Fns`): its streaming functions, HMAC's `init` and `finalize`
and PBKDF2's `iterate` for it, by the names they are registered with; and
`pbkdf2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`), which
the registration files' `spSafe` checks evaluate.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Hmac.Generic.X86

/-- The functions `pbkdf2` calls for the hash function `H` of the instance
`I`, with the working space of `I`'s functions. -/
def fnsOf (I : Spec.Hmac.Instance) (H : Impl.Hmac.Generic.X86.Hash) : Fns where
  H := H
  W := I.scratch
  hiN := I.initApi.name
  hiC := H.init
  hfN := I.finalizeApi.name
  hfC := H.finalize
  itN := I.iterateApi.name
  itC := Impl.Pbkdf2.Generic.X86.iterate H

def sha1F : Fns := fnsOf Spec.Hmac.sha1I sha1H
def md5F : Fns := fnsOf Spec.Hmac.md5I md5H
def sha384F : Fns := fnsOf Spec.Hmac.sha384I sha384H
def sha512F : Fns := fnsOf Spec.Hmac.sha512I sha512H'
def sha512_224F : Fns := fnsOf Spec.Hmac.sha512_224I sha512_224H
def sha512_256F : Fns := fnsOf Spec.Hmac.sha512_256I sha512_256H

materialize_code sha1Pbkdf2 := sha1F.pbkdf2
materialize_code md5Pbkdf2 := md5F.pbkdf2
materialize_code sha384Pbkdf2 := sha384F.pbkdf2
materialize_code sha512Pbkdf2 := sha512F.pbkdf2
materialize_code sha512_224Pbkdf2 := sha512_224F.pbkdf2
materialize_code sha512_256Pbkdf2 := sha512_256F.pbkdf2

end VG.Proof.Pbkdf2.Whole.X86
