import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Argon2.X86.Compress

/-!
# Argon2 compression on x86 (32-bit): the code as a literal

The compression function is fully unrolled: its literal (`materialize_code`)
spares the kernel building the instructions in every check that evaluates
the code (constant time, `spSafe`), and its callers call it.
-/

namespace VG.Impl.Argon2.X86

materialize_code compress

end VG.Impl.Argon2.X86
