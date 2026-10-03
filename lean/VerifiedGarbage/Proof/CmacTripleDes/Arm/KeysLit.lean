import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.Arm.roundKeys

theorem Proof.CmacTripleDes.Arm.roundKeys_eq :
    Impl.CmacTripleDes.Arm.roundKeys = Impl.CmacTripleDes.Arm.roundKeys.lit :=
  Impl.CmacTripleDes.Arm.roundKeys.lit_eq

end VG
