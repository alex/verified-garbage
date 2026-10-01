import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X448.X86

/-!
# X448 on x86 (32-bit): the code as a literal

Untrusted: everything here is checked by Lean. The field arithmetic is fully
unrolled: the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`) spares the kernel building
the instructions again in every check that evaluates the code (constant
time, `spSafe`).
-/

namespace VG.Impl.X448.X86

materialize_code x448

end VG.Impl.X448.X86
