import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes
import VerifiedGarbage.Impl.Pbkdf2.Generic.X86

/-!
# HMAC and PBKDF2 over every hash on X86: the code as literals

HMAC's `init` and `finalize` and PBKDF2's `iterate` at each hash function, as
literals (`materialize_code`, `Proof/Framework/Lit.lean`) that refer to the
hash functions' literals: the registration files' `spSafe` checks evaluate
them.
-/

namespace VG.Proof.Hmac.Generic.X86

materialize_code sha1HInit := sha1H.init
materialize_code sha1HFinalize := sha1H.finalize
materialize_code md5HInit := md5H.init
materialize_code md5HFinalize := md5H.finalize
materialize_code sha384HInit := sha384H.init
materialize_code sha384HFinalize := sha384H.finalize
materialize_code sha512HInit := sha512H'.init
materialize_code sha512HFinalize := sha512H'.finalize
materialize_code sha512_224HInit := sha512_224H.init
materialize_code sha512_224HFinalize := sha512_224H.finalize
materialize_code sha512_256HInit := sha512_256H.init
materialize_code sha512_256HFinalize := sha512_256H.finalize
materialize_code sha1HIterate := Impl.Pbkdf2.Generic.X86.iterate sha1H
materialize_code md5HIterate := Impl.Pbkdf2.Generic.X86.iterate md5H
materialize_code sha384HIterate := Impl.Pbkdf2.Generic.X86.iterate sha384H
materialize_code sha512HIterate := Impl.Pbkdf2.Generic.X86.iterate sha512H'
materialize_code sha512_224HIterate := Impl.Pbkdf2.Generic.X86.iterate sha512_224H
materialize_code sha512_256HIterate := Impl.Pbkdf2.Generic.X86.iterate sha512_256H

end VG.Proof.Hmac.Generic.X86
