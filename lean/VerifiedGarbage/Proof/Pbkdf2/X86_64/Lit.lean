import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# PBKDF2-HMAC's iteration on x86-64: the code as literals

Untrusted: everything here is checked by Lean. The iteration at each hash
function with one implementation of its compression function (MD5), as
literals (`materialize_code`, `Proof/Framework/Lit.lean`) that refer to the
compression functions' literals: the checks of its instructions and the
registration files' `spSafe` evaluate them. (The iterations over SHA-1,
SHA-256 and the SHA-512 family are proven for any implementation `v` of the
compression function, from checks that do not evaluate its code.)
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG.Impl.Pbkdf2.X86_64 (iterate)

materialize_code md5Iterate :=
  iterate Impl.Md5.X86_64.Stream.params 16 "vg_md5_compress" Impl.Md5.X86_64.compress

end VG.Proof.Pbkdf2.X86_64
