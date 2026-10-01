import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CT
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Contract
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Lit

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem signCached_verified : Verified X86.target code (Spec.Ed25519.signCachedContract X86.abi 280) := by
  have hsat := signWide_implies.sat_left
  have satLocal : ∃ s, signCachedLocal.pre s := hsat.elim fun s h => ⟨_, signWide_pre s h⟩
  have verifiedLocal : Verified X86.target code signCachedLocal :=
    Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal signRd signWr signWide_pre
    ?_ ?_ ?_ ?_ hsat) signWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.SignCached
