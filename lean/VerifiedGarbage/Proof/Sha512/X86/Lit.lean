import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha512.X86.Stream

/-!
# SHA-512 on x86 (32-bit): the code as literals

The compression function is fully unrolled (15,000 instructions): its
literal (`materialize_code`) spares the kernel building the instructions in
every check that evaluates the code (constant time, `spSafe`), and the
streaming functions call it.
-/

namespace VG.Impl.Sha512.X86

materialize_code compress
materialize_code Stream.update
materialize_code Stream.finalize

end VG.Impl.Sha512.X86
