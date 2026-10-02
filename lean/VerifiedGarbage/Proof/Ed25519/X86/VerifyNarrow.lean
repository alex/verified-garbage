import VerifiedGarbage.Proof.Ed25519.X86.VerifyWide

namespace VG.Proof.Ed25519.X86
open VG VG.X86

theorem verifyNarrow_read (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyRd s ++ verifyWr s) a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.1, h.2.1]
  simp only [verifyRd, verifyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩
  · refine ⟨scR 8192 (arg s 3), by simp, ?_⟩
    simp only [addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

theorem verifyNarrow_write (s : State) (h : verifyWide.pre s) (a : Addr) (n : Nat)
    (hr : InRegions (verifyWr s) a n) : InRegions s.wr a n := by
  obtain ⟨r, hr, hc⟩ := hr
  rw [h.2.1]
  simp only [verifyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨scR 8192 (arg s 3), by simp, ?_⟩
    simp only [addr_zero, Region.Contains] at hc ⊢
    omega_using [hc]
  · exact ⟨_, by simp, hc⟩

end VG.Proof.Ed25519.X86
