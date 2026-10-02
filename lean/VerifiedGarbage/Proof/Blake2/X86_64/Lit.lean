import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Blake2.X86_64

/-!
# BLAKE2 on x86-64: the code as literals

The code of the compression functions of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG.Proof.Blake2.X86_64

materialize_code compressB := Impl.Blake2.X86_64.compress Spec.Blake2.b
materialize_code compressS := Impl.Blake2.X86_64.compress Spec.Blake2.s

end VG.Proof.Blake2.X86_64
