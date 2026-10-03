import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.X86_64.roundKeys

theorem Proof.CmacTripleDes.X86_64.roundKeys_eq :
    Impl.CmacTripleDes.X86_64.roundKeys = Impl.CmacTripleDes.X86_64.roundKeys.lit :=
  Impl.CmacTripleDes.X86_64.roundKeys.lit_eq

end VG
