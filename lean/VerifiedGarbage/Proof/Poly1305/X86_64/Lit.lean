import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64

/-!
# Poly1305 on X86_64: the code as literals

Untrusted: everything here is checked by Lean. The code of the functions
below as literals (`materialize_code`, `Proof/Framework/Lit.lean`): the
kernel checks each literal once here, and then evaluates it, rather than
building the instructions again, in every check that evaluates the code
(constant time, `spSafe`, properties of every instruction), including those
of its callers.
-/

namespace VG

materialize_code Impl.Poly1305.X86_64.init
materialize_code Impl.Poly1305.X86_64.blocks
materialize_code Impl.Poly1305.X86_64.updatePre
materialize_code Impl.Poly1305.X86_64.updatePost
materialize_code Impl.Poly1305.X86_64.finalize

end VG
