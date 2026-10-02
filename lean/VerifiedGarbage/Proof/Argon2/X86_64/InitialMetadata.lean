import VerifiedGarbage.Proof.Argon2.X86_64.Initial

/-! H₀ writes its digest into the frame while retaining all enclosing arguments. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64

theorem Finished.rbp {s t : State} (h : Finished s t) : t.gpr .rbp = s.gpr .rbp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rbx {s t : State} (h : Finished s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.rsp {s t : State} (h : Finished s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide) (by decide) (by decide)

theorem Finished.frame_word {s t : State} (h : Finished s t) (space : Space s)
    (d : Nat) (bound : d + 8 ≤ 272) (afterDigest : 64 ≤ d) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.rbp]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact space.frameWork.sub_left (Offset.sub_base _ bound) |>.sub_right
      (Region.sub_prefix (by decide))
  · exact space.frameStack.sub_left (Offset.sub_base _ bound)
  · simpa only [BitVec.add_zero] using
      Offset.disjoint (s.gpr .rbp) (d := d) (n := 8) (e := 0) (k := 64)
        (Or.inr afterDigest) (by omega) (by decide)

end VG.Proof.Argon2.X86_64.Initial
