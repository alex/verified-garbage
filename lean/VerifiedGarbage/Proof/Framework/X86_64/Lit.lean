import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# XReg code as literals

Untrusted: everything here is checked by Lean. The instances `materialize_code`
needs to write this ISA's code as a literal (`Proof/Framework/Lit.lean`).
-/

namespace VG.X86_64

deriving instance Lean.ToExpr for XReg
deriving instance Lean.ToExpr for MemOp
deriving instance Lean.ToExpr for VLen
deriving instance Lean.ToExpr for Src
deriving instance Lean.ToExpr for AluOp
deriving instance Lean.ToExpr for ShiftOp
deriving instance Lean.ToExpr for XBinOp
deriving instance Lean.ToExpr for XShiftOp
deriving instance Lean.ToExpr for XOp
deriving instance Lean.ToExpr for VBinOp
deriving instance Lean.ToExpr for VVarOp
deriving instance Lean.ToExpr for VOp
deriving instance Lean.ToExpr for ZBinOp
deriving instance Lean.ToExpr for ZOp
deriving instance Lean.ToExpr for ZBcstOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.X86_64
