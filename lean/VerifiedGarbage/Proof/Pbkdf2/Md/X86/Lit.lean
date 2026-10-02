import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Hashes

/-!
# HMAC's `init` and `finalize` and PBKDF2's `iterate` on x86 (32-bit): the code as literals

`Hash.hmacInit`, `Hash.hmacFin` and `Hash.iterate` (`Impl/Pbkdf2/Md/X86.lean`) at each hash
function of `Hashes.lean`, as literals (`materialize_code`,
`Proof/Framework/Lit.lean`) that refer to the literals of the functions they
call (the compression functions, and the streaming `init` and `finalize`): the
registration files' `spSafe` checks evaluate them.
-/

namespace VG.Proof.Pbkdf2.Md.X86

materialize_code md5MInit := md5M.hmacInit
materialize_code md5MFinalize := md5M.hmacFin
materialize_code md5MIterate := md5M.iterate
materialize_code sha1MInit := sha1M.hmacInit
materialize_code sha1MFinalize := sha1M.hmacFin
materialize_code sha1MIterate := sha1M.iterate
materialize_code sha384MInit := sha384M.hmacInit
materialize_code sha384MFinalize := sha384M.hmacFin
materialize_code sha384MIterate := sha384M.iterate
materialize_code sha512MInit := sha512M'.hmacInit
materialize_code sha512MFinalize := sha512M'.hmacFin
materialize_code sha512MIterate := sha512M'.iterate
materialize_code sha512_224MInit := sha512_224M.hmacInit
materialize_code sha512_224MFinalize := sha512_224M.hmacFin
materialize_code sha512_224MIterate := sha512_224M.iterate
materialize_code sha512_256MInit := sha512_256M.hmacInit
materialize_code sha512_256MFinalize := sha512_256M.hmacFin
materialize_code sha512_256MIterate := sha512_256M.iterate

end VG.Proof.Pbkdf2.Md.X86
