import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt

/-!
# ML-DSA on AArch64: the code of the NTTs as literals

Untrusted: everything here is checked by Lean. The code of `ntt` and
`nttInv`, whose tables of zetas are built by functions, as literals
(`materialize_code`, `Proof/Framework/Lit.lean`): the kernel checks each
literal once here, and then evaluates it, rather than building the
instructions again, in every check that evaluates the code (constant time,
`spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.MlDsa.AArch64.Arith.ntt
materialize_code Impl.MlDsa.AArch64.Arith.nttInv

end VG
