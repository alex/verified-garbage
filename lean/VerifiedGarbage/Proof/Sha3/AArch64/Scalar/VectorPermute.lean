import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorPermute
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ControlVector
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

/-- The vector-slot alternative has the same public permutation contract. -/
theorem vector_permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa vectorPermute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (Control.middle vectorCoreInstrs) Control.middle_vector_ok s
    (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem vector_permute_noCalls : vectorPermute.noCalls = true := by lit_decide
theorem vector_permute_noFrames : vectorPermute.noFrames = true := by lit_decide

theorem vector_permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre
    VG.Proof.Sha3.permuteAArch64.pub vectorPermute := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem vector_permute_verified :
    Verified AArch64.target vectorPermute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct vector_permute_correct vector_permute_ct (by
    sig_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, VG.Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState]
      using VG.Proof.Sha3.AArch64.satState)

#assert_standard_axioms vector_permute_correct
#assert_standard_axioms vector_permute_ct
#assert_standard_axioms vector_permute_verified
end VG.Proof.Sha3.AArch64.Scalar
