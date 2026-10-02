import VerifiedGarbage.Proof.Argon2.AArch64.RandomSource

/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : Ready p pass lane slice index old s) (done : Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.RandomSource
