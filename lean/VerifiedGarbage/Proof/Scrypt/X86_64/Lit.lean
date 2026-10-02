import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-!
# scrypt on X86_64: the code as literals

The code of the functions below as literals (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks each literal once here, and
then evaluates it, rather than building the instructions again, in every check
that evaluates the code (constant time, `spSafe`, properties of every
instruction), including those of its callers.
-/

namespace VG

materialize_code Impl.Scrypt.X86_64.salsa
materialize_code Impl.Scrypt.X86_64.blockMix
materialize_code Impl.Scrypt.X86_64.roMix

end VG
