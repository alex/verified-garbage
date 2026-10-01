import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CT
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Contract
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Lit

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

theorem verifyMessage_verified : Verified X86.target code (Spec.Ed25519.verifyContract X86.abi 280) := by
  have hsat := verifyWide_implies.sat_left
  have satLocal : ∃ s, verifyMessageLocal.pre s := hsat.elim fun s h => ⟨_, verifyWide_pre s h⟩
  have verifiedLocal : Verified X86.target code verifyMessageLocal :=
    Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal verifyRd verifyWr verifyWide_pre
    ?_ ?_ ?_ ?_ hsat) verifyWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [verifyWr, List.mem_singleton] at hr
    subst hr
    simp
  · intro s t _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_mem,
      State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [verifyWide, verifyMessageLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_mem] using h

end VG.Proof.Ed25519.X86.VerifyMessage
