import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86.Round

/-! # The key schedule's code as a literal, for kernel-evaluated checks -/

namespace VG.Proof.CmacTripleDes.X86

open VG.X86

materialize_code keysCode := (Code.block Impl.CmacTripleDes.X86.roundKeys : Prog isa)

theorem roundKeys_eq : Impl.CmacTripleDes.X86.roundKeys = instrs keysCode.lit :=
  congrArg instrs keysCode.lit_eq

end VG.Proof.CmacTripleDes.X86
