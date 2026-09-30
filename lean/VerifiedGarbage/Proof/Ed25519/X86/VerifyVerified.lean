import VerifiedGarbage.Proof.Ed25519.X86.VerifyNarrow
import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit

/-! Untrusted: transfer the verifier from its framed local contract to the reviewed ABI. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verify_verified_of_correct
    (correct : ∀ s, verifyLocal.pre s → WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t)
    (ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation) :
    Verified X86.target verifyEquation (Spec.Ed25519.verifyEquationContract X86.abi) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation verifyLocal :=
    Verified.of_correct correct ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    verifyNarrow_read verifyNarrow_write ?_ ?_ hsat) verifyWide_implies
  · intro s t _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyLocal, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

end VG.Proof.Ed25519.X86
