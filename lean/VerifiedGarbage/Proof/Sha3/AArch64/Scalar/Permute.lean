import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ControlCore

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

/-- The register-resident implementation preserves the complete ABI and
implements the same public permutation contract as the prior scalar core. -/
theorem permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (Control.middle coreInstrs) Control.middle_core_ok s
    (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem permute_noCalls : permute.noCalls = true := by lit_decide
theorem permute_noFrames : permute.noFrames = true := by lit_decide

#assert_standard_axioms permute_correct
end VG.Proof.Sha3.AArch64.Scalar
