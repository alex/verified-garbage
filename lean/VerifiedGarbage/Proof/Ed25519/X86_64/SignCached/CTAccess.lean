import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CTFramework

/-! Memory coverage for modular constant-time calls in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (within_base within_off add_add)

theorem init_access (L : Lay) (_hL : L.Ok) : Access L initRd (initWr L) := by
  constructor
  · intro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [initWr, List.mem_singleton] at hr; subst hr
    exact .inr (.inr (within_base _ (by omega)))

theorem upd_access (L : Lay) (p : Addr) (n : BitVec 64) (hi : Input L ⟨p, n.toNat⟩) :
    Access L [⟨p, n.toNat⟩] (updWr L) := by
  constructor
  · intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inr (.inr (within_off _ (by omega)))

theorem fin_access (L : Lay) (_hL : L.Ok) : Access L [] (finWr L) := by
  constructor
  · intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inl ⟨128, by rw [add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega)))

theorem reduce_access (out : Nat) (ho : out + 32 ≤ 128) (L : Lay) (_hL : L.Ok) :
    Access L (reduceRd L) (reduceWr L out) := by
  constructor
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega⟩
    · exact .inr (.inr (within_base _ (by omega)))

theorem base_access (L : Lay) (_hL : L.Ok) : Access L (baseRd L) (baseWr L) := ⟨base_sub, base_wsub⟩

theorem mul_access (L : Lay) (_hL : L.Ok) : Access L (mulRd L) (mulWr L) := by
  constructor
  · intro r hr
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega)))
    · exact .inr (.inr (within_base _ (by omega)))

end VG.Proof.Ed25519.X86_64.SignCached
