import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.ChaCha20.X86.Xor

/-!
# ChaCha20 on X86: the code as literals

The code of the functions below as literals (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks each literal once here, and
then evaluates it, rather than building the instructions again, in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction), including those of its callers.
-/

namespace VG

materialize_code Impl.ChaCha20.X86.block
materialize_code Impl.ChaCha20.X86.Xor.xor

end VG
