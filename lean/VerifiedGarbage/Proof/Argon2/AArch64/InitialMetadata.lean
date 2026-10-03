import VerifiedGarbage.Proof.Argon2.AArch64.Initial

/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64

theorem Finished.x19 {s t : State} (h : Finished s t) : t.gpr .x19 = s.gpr .x19 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.x24 {s t : State} (h : Finished s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : Finished s t) (space : Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.x19]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .x19) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega) (by decide)

end VG.Proof.Argon2.AArch64.Initial
