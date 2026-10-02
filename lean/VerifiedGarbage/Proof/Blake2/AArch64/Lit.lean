import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Blake2.AArch64

/-!
# BLAKE2 on AArch64: the code as literals

The code of the compression functions of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG.Proof.Blake2.AArch64

materialize_code compressB := Impl.Blake2.AArch64.compress Spec.Blake2.b
materialize_code compressS := Impl.Blake2.AArch64.compress Spec.Blake2.s

end VG.Proof.Blake2.AArch64
