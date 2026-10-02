import VerifiedGarbage.Proof.Argon2.AArch64.DeriveBodyCorrect

/-! The whole body leaves the prologue's six saved-register slots untouched. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def savedSlot (s : State) (j : Nat) : Region :=
  ⟨s.sp - BitVec.ofNat 64 (16 * (j + 1)), 8⟩

theorem saved_slot_sub (s : State) (j : Nat) (bound : j < 7) :
    Region.Sub (savedSlot s j) (below (s.sp) 400) :=
  Offset.sub_below _ (by omega) (by omega)

theorem saved_slot_address (s : State) (j : Nat) (bound : j < 7) :
    (savedSlot s j).base = (prologueState s).sp + BitVec.ofNat 64 (384 - 16 * (j + 1)) := by
  rw [prologue_sp]
  exact Offset.sub_ofNat_eq _ (by omega)

theorem saved_slot_buffers {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 7)
    (buffer : Region × Bool) (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (savedSlot s j).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (saved_slot_sub s j bound)

theorem saved_slot_writes {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 7) :
    ∀ r ∈ bodyWrites s, (savedSlot s j).Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · apply saved_slot_buffers h j bound (abiMatrix s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply saved_slot_buffers h j bound (abiWork s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply saved_slot_buffers h j bound (abiOutput s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · change (⟨(savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [saved_slot_address s j bound]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · change (⟨(savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [saved_slot_address s j bound]
    exact Offset.disjoint_below _ (by omega)

theorem BodyDone.saved {s t : State} (h : AbiEnvironment s) (done : BodyDone s t) (j : Nat) (bound : j < 7) :
    t.mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 =
      (prologueState s).mem.readW (s.sp - BitVec.ofNat 64 (16 * (j + 1))) 64 :=
  done.frame.readW (r := savedSlot s j) (Region.contains_self _ _) (saved_slot_writes h j bound) (by decide)

end VG.Proof.Argon2.AArch64.Derive
