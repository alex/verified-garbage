import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

theorem laneReg_injective : ∀ i < 25, ∀ j < 25,
    laneReg i = laneReg j → i = j := by decide +kernel

theorem thetaReg_injective : ∀ i < 25, ∀ j < 25,
    thetaReg i = thetaReg j → i = j := by decide +kernel

theorem scratch_not_lane : ∀ r ∈ [Reg.x26, .x27, .x28, .x30],
    ∀ i < 25, laneReg i ≠ r := by decide +kernel

/-- These operand constraints allow a baseline-ISA implementation of BIC
as AND then XOR, and EOR-with-rotation without destroying a live source. -/
def BaselineSafe : ScalarOp → Prop
  | .bic d a _ => d ≠ a
  | .bicRor d a b _ => d ≠ a ∧ d ≠ b
  | .xorRor d a b _ => a ≠ b ∧ d ≠ b
  | .spill k _ => k < 2
  | .reload _ k => k < 2
  | _ => True

instance (op : ScalarOp) : Decidable (BaselineSafe op) := by
  cases op <;> unfold BaselineSafe <;> infer_instance

theorem baseline_safe : ∀ op ∈ thetaOps ++ rhoPiOps ++ chiOps,
    BaselineSafe op := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar
