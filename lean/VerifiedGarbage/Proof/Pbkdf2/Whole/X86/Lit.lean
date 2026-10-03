import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its code as literals

For each hash function of `Proof/Pbkdf2/Md/X86/Hashes.lean`, the functions
`pbkdf2` calls (`Fns`): its streaming functions, HMAC's `init` and
`finalize` and PBKDF2's `iterate` (`Impl/Pbkdf2/Md/X86.lean`) for it, by the names they are registered with; and
`pbkdf2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`), which
the registration files' `spSafe` checks evaluate.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Pbkdf2.Md.X86

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I`, with the working space of `I`'s functions. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.X86.Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := I.initApi.name
  hiC := M.hmacInit
  hfN := I.finalizeApi.name
  hfC := M.hmacFin
  itN := I.iterateApi.name
  itC := M.iterate

def sha1F : Fns := fnsOf Spec.Hmac.sha1I sha1M
def md5F : Fns := fnsOf Spec.Hmac.md5I md5M
def sha384F : Fns := fnsOf Spec.Hmac.sha384I sha384M
def sha512F : Fns := fnsOf Spec.Hmac.sha512I sha512M'
def sha512_224F : Fns := fnsOf Spec.Hmac.sha512_224I sha512_224M
def sha512_256F : Fns := fnsOf Spec.Hmac.sha512_256I sha512_256M

materialize_code sha1Pbkdf2 := sha1F.pbkdf2
materialize_code md5Pbkdf2 := md5F.pbkdf2
materialize_code sha384Pbkdf2 := sha384F.pbkdf2
materialize_code sha512Pbkdf2 := sha512F.pbkdf2
materialize_code sha512_224Pbkdf2 := sha512_224F.pbkdf2
materialize_code sha512_256Pbkdf2 := sha512_256F.pbkdf2

end VG.Proof.Pbkdf2.Whole.X86
