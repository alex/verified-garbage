import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Sha512.X86_64.ShaNi

/-!
# SHA-512 with the SHA512 extension on x86-64: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`): the kernel checks it once here, and then
evaluates it, rather than building the instructions again, in every check that
evaluates the code (constant time, `spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.Sha512.X86_64.ShaNi.compress

end VG
