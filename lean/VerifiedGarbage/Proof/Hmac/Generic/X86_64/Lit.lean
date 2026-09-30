import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hashes

/-!
# HMAC over every hash on X86_64: the code as literals

Untrusted: everything here is checked by Lean. HMAC's `init` and `finalize`
at each hash function with one implementation of its compression function
(MD5), as literals (`materialize_code`, `Proof/Framework/Lit.lean`) that
refer to the hash functions' literals: the registration files' `spSafe`
checks evaluate them. (Those over SHA-1 and the SHA-512 family are proven
for any implementation `v` of the compression function, from checks that do
not evaluate its code.)
-/

namespace VG.Proof.Hmac.Generic.X86_64

-- MD5's functions first (no module of MD5's materializes them), so that the
-- literals below call their literals rather than repeating their code.
materialize_code md5Compress := Impl.Md5.X86_64.compress
materialize_code md5Update := Impl.Md5.X86_64.Stream.update
materialize_code md5Finalize := Impl.Md5.X86_64.Stream.finalize
materialize_code md5HInit := md5H.init
materialize_code md5HFinalize := md5H.finalize

end VG.Proof.Hmac.Generic.X86_64
