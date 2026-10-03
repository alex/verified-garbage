import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# VReg code as literals

The instances `materialize_code` needs to write this ISA's code as a literal
(`Proof/Framework/Lit.lean`).
-/

namespace VG.AArch64

deriving instance Lean.ToExpr for VReg
deriving instance Lean.ToExpr for Size
deriving instance Lean.ToExpr for LogicOp
deriving instance Lean.ToExpr for VArr
deriving instance Lean.ToExpr for VLogicOp
deriving instance Lean.ToExpr for VShiftOp
deriving instance Lean.ToExpr for VPermOp
deriving instance Lean.ToExpr for VRevOp
deriving instance Lean.ToExpr for Sha1Op
deriving instance Lean.ToExpr for VOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.AArch64
