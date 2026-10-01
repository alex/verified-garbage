import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

instance (op : ScalarOp) : Decidable (Good op) := by
  cases op <;> unfold Good <;> infer_instance

theorem core_good : ∀ op ∈ coreOps, Good op := by decide +kernel

theorem core_math (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds laneReg (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))
      (run coreOps f) := by
  have hm := chi_correct _ _ (rhoPi_correct _ _ (theta_correct A f h))
  simpa only [coreOps, run, List.foldl_append] using hm

end VG.Proof.Sha3.AArch64.Scalar
