import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Shift code as literals

The instances `materialize_code` needs to write this ISA's code as a literal
(`Proof/Framework/Lit.lean`).
-/

namespace VG.Arm

deriving instance Lean.ToExpr for Shift
deriving instance Lean.ToExpr for Op2
deriving instance Lean.ToExpr for DpOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.Arm
