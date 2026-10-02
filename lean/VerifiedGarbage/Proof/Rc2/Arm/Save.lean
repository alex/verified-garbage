import VerifiedGarbage.Proof.Rc2.Arm.BlockStore
import VerifiedGarbage.Proof.Rc2.Arm.MemOps
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-! # Where RC2 (and TDEA) save their callee-saved registers in scratch

The `i`th register of a list at byte `4 * i`; the saving and restoring are
`VG.Arm.Spill`'s. -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

/-- Each register of `regs`, the `i`th at byte `4 * i`. -/
def slotsOf (regs : List Reg) : List (Reg × Nat) := regs.zipIdx.map fun (r, i) => (r, 4 * i)

end VG.Proof.Rc2.Arm
