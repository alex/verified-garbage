import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes

/-!
# HMAC over every hash on X86: `init` as literals

Untrusted: everything here is checked by Lean. HMAC's `init` at each hash
function, as literals (`materialize_code`, `Proof/Framework/Lit.lean`) that
refer to the hash functions' literals: the registration files' `spSafe`
checks evaluate them. `finalize` and PBKDF2's `iterate`, written over the
compression function, are in `Proof/Pbkdf2/Md/X86/Lit.lean`.
-/

namespace VG.Proof.Hmac.Generic.X86

materialize_code sha1HInit := sha1H.init
materialize_code md5HInit := md5H.init
materialize_code sha384HInit := sha384H.init
materialize_code sha512HInit := sha512H'.init
materialize_code sha512_224HInit := sha512_224H.init
materialize_code sha512_256HInit := sha512_256H.init

end VG.Proof.Hmac.Generic.X86
