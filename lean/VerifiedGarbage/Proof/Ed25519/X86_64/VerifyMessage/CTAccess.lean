import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CTFramework

/-! The regions passed to the verifier's subroutines. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG
open VG.Proof.Ed25519.X86_64.PublicKey (within_base within_off add_add)

theorem init_access (L : Lay) : Access L initRd (initWr L) where
  sub := by
    intro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr
    subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [initWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))

theorem upd_access (L : Lay) (p : Addr) (n : BitVec 64) (hi : Input L ⟨p, n.toNat⟩) :
    Access L [⟨p, n.toNat⟩] (updWr L) where
  sub := by
    intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hs⟩ := hi
      exact ⟨R, List.mem_append_left _ hR, hs⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inr (within_off _ (by omega))

theorem fin_access (L : Lay) : Access L [] (finWr L) where
  sub := by
    intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (within_base _ (by omega))
    · exact .inl ⟨64, by rw [add_add], by show 64 + 64 ≤ 128; decide⟩
    · exact .inr (within_off _ (by omega))

theorem reduce_access (L : Lay) : Access L (reduceRd L) (reduceWr L) where
  sub := by
    intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (within_base _ (by omega))
    · exact .inr (within_base _ (by omega))

theorem eq_access (L : Lay) : Access L (eqRd L) (eqWr L) where
  sub := by
    intro r hr
    simp only [eqRd, eqWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  wsub := by
    intro r hr
    simp only [eqWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))

end VG.Proof.Ed25519.X86_64.VerifyMessage
