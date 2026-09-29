import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# x86 (32-bit) code as literals

Untrusted: everything here is checked by Lean. The instances `materialize_code`
needs to write x86 code as a literal (`Proof/Framework/Lit.lean`).
-/

namespace VG.X86

deriving instance Lean.ToExpr for MemOp
deriving instance Lean.ToExpr for Reg8
deriving instance Lean.ToExpr for Src
deriving instance Lean.ToExpr for AluOp
deriving instance Lean.ToExpr for ShiftOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.X86
