import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CT
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Contract
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Lit

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem publicKey_verified : Verified X86.target publicKey (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkLocal.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKey pkLocal :=
    Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.PublicKey
