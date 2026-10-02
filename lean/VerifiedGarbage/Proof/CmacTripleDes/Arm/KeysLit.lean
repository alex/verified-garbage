import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round

/-! # The key schedule's code as a literal, for kernel-evaluated checks -/

namespace VG.Proof.CmacTripleDes.Arm

open VG.Arm

materialize_code keysCode := (Code.block Impl.CmacTripleDes.Arm.roundKeys : Prog isa)

theorem roundKeys_eq : Impl.CmacTripleDes.Arm.roundKeys = instrs keysCode.lit :=
  congrArg instrs keysCode.lit_eq

end VG.Proof.CmacTripleDes.Arm
