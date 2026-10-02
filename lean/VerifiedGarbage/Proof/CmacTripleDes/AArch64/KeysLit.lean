import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round

/-! # The key schedule's code as a literal, for kernel-evaluated checks -/

namespace VG.Proof.CmacTripleDes.AArch64

open VG.AArch64

materialize_code keysCode := (Code.block Impl.CmacTripleDes.AArch64.roundKeys : Prog isa)

theorem roundKeys_eq : Impl.CmacTripleDes.AArch64.roundKeys = instrs keysCode.lit :=
  congrArg instrs keysCode.lit_eq

end VG.Proof.CmacTripleDes.AArch64
